{-# LANGUAGE ViewPatterns, BangPatterns, CPP, NondecreasingIndentation, ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards, TupleSections #-}
{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}
-- NB: we specifically ignore deprecations. GHC 7.6 marks the .QSem module as
-- deprecated, although it became un-deprecated later. As a result, using 7.6
-- as your bootstrap compiler throws annoying warnings.

-- -----------------------------------------------------------------------------
--
-- (c) The University of Glasgow, 2011
--
-- This module implements multi-module compilation, and is used
-- by --make and GHCi.
--
-- -----------------------------------------------------------------------------
module GhcMake(
        depanal,
        load, load', LoadHowMuch(..),

        topSortModuleGraph,

        ms_home_srcimps, ms_home_imps,

        IsBoot(..),
        summariseModule,
        hscSourceToIsBoot,
        findExtraSigImports,
        implicitRequirements,

        noModError, cyclicModuleErr,
        moduleGraphNodes, SummaryNode
    ) where

#include "HsVersions.h"

import MakeQueue
import qualified Linker         ( unload )

import DriverPhases
import DriverPipeline
import DynFlags
import ErrUtils
import Finder
import GhcMonad
import HeaderInfo
import HscTypes
import Module
import TcIface          ( typecheckIface )
import TcRnMonad        ( initIfaceCheck )
import HscMain

import Bag              ( listToBag )
import BasicTypes
import Digraph
import Exception        ( tryIO, gbracket)
import FastString
import Maybes           ( expectJust )
import Name
import MonadUtils       ( MonadIO )
import Outputable
import Panic
import SrcLoc
import StringBuffer
import UniqFM
-- import UniqDSet
import TcBackpack
import Packages
import UniqSet
import Util
import qualified GHC.LanguageExtensions as LangExt
import NameEnv
import FileCleanup

import Data.Either ( rights, partitionEithers )
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified FiniteMap as Map ( insertListWith )
-- import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Control.Concurrent ( forkIOWithUnmask, killThread )
import qualified GHC.Conc as CC
import Control.Concurrent.MVar
-- import Control.Concurrent.QSem
import Control.Exception
import Control.Monad
import Data.IORef
import Data.List
import Data.Foldable
import qualified Data.List as List
import Data.Traversable
import Data.Maybe
-- import Data.Ord ( comparing )
import Data.Time
import System.Directory
import System.FilePath
import System.IO        ( fixIO )
import System.IO.Error  ( isDoesNotExistError )
import Control.Concurrent.Chan
import GHC.Conc ( getNumProcessors, getNumCapabilities, setNumCapabilities )
import Data.Typeable
-- import Data.Either

label_self :: String -> IO ()
label_self thread_name = do
    self_tid <- CC.myThreadId
    CC.labelThread self_tid thread_name

-- -----------------------------------------------------------------------------
-- Loading the program

-- | Perform a dependency analysis starting from the current targets
-- and update the session with the new module graph.
--
-- Dependency analysis entails parsing the @import@ directives and may
-- therefore require running certain preprocessors.
--
-- Note that each 'ModSummary' in the module graph caches its 'DynFlags'.
-- These 'DynFlags' are determined by the /current/ session 'DynFlags' and the
-- @OPTIONS@ and @LANGUAGE@ pragmas of the parsed module.  Thus if you want
-- changes to the 'DynFlags' to take effect you need to call this function
-- again.
--
depanal :: GhcMonad m =>
           [ModuleName]  -- ^ excluded modules
        -> Bool          -- ^ allow duplicate roots
        -> m ModuleGraph
depanal excluded_mods allow_dup_roots = do
  hsc_env <- getSession
  let
         dflags  = hsc_dflags hsc_env
         targets = hsc_targets hsc_env
         old_graph = hsc_mod_graph hsc_env

  withTiming (pure dflags) (text "Chasing dependencies") (const ()) $ do
    liftIO $ debugTraceMsg dflags 2 (hcat [
              text "Chasing modules from: ",
              hcat (punctuate comma (map pprTarget targets))])

    -- Home package modules may have been moved or deleted, and new
    -- source files may have appeared in the home package that shadow
    -- external package modules, so we have to discard the existing
    -- cached finder data.
    liftIO $ flushFinderCaches hsc_env

    mod_summariesE <- liftIO $ downsweep hsc_env (mgModSummaries old_graph)
                                     excluded_mods allow_dup_roots
    mod_summaries <- reportImportErrors mod_summariesE

    let mod_graph = mkModuleGraph mod_summaries

    warnMissingHomeModules hsc_env mod_graph

    setSession hsc_env { hsc_mod_graph = mod_graph }
    return mod_graph

-- Note [Missing home modules]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Sometimes user doesn't want GHC to pick up modules, not explicitly listed
-- in a command line. For example, cabal may want to enable this warning
-- when building a library, so that GHC warns user about modules, not listed
-- neither in `exposed-modules`, nor in `other-modules`.
--
-- Here "home module" means a module, that doesn't come from an other package.
--
-- For example, if GHC is invoked with modules "A" and "B" as targets,
-- but "A" imports some other module "C", then GHC will issue a warning
-- about module "C" not being listed in a command line.
--
-- The warning in enabled by `-Wmissing-home-modules`. See Trac #13129
warnMissingHomeModules :: GhcMonad m => HscEnv -> ModuleGraph -> m ()
warnMissingHomeModules hsc_env mod_graph =
    when (wopt Opt_WarnMissingHomeModules dflags && not (null missing)) $
        logWarnings (listToBag [warn])
  where
    dflags = hsc_dflags hsc_env
    targets = map targetId (hsc_targets hsc_env)

    is_known_module mod = any (is_my_target mod) targets

    -- We need to be careful to handle the case where (possibly
    -- path-qualified) filenames (aka 'TargetFile') rather than module
    -- names are being passed on the GHC command-line.
    --
    -- For instance, `ghc --make src-exe/Main.hs` and
    -- `ghc --make -isrc-exe Main` are supposed to be equivalent.
    -- Note also that we can't always infer the associated module name
    -- directly from the filename argument.  See Trac #13727.
    is_my_target mod (TargetModule name)
      = moduleName (ms_mod mod) == name
    is_my_target mod (TargetFile target_file _)
      | Just mod_file <- ml_hs_file (ms_location mod)
      = target_file == mod_file ||
           --  We can get a file target even if a module name was
           --  originally specified in a command line because it can
           --  be converted in guessTarget (by appending .hs/.lhs).
           --  So let's convert it back and compare with module name
           mkModuleName (fst $ splitExtension target_file)
            == moduleName (ms_mod mod)
    is_my_target _ _ = False

    missing = map (moduleName . ms_mod) $
      filter (not . is_known_module) (mgModSummaries mod_graph)

    msg
      | gopt Opt_BuildingCabalPackage dflags
      = text "These modules are needed for compilation but not listed in your .cabal file's other-modules: "
        <> sep (map ppr missing)
      | otherwise
      = text "Modules are not listed in command line but needed for compilation: "
        <> sep (map ppr missing)
    warn = makeIntoWarning
      (Reason Opt_WarnMissingHomeModules)
      (mkPlainErrMsg dflags noSrcSpan msg)

-- | Describes which modules of the module graph need to be loaded.
data LoadHowMuch
   = LoadAllTargets
     -- ^ Load all targets and its dependencies.
   | LoadUpTo ModuleName
     -- ^ Load only the given module and its dependencies.
   | LoadDependenciesOf ModuleName
     -- ^ Load only the dependencies of the given module, but not the module
     -- itself.

-- | Try to load the program.  See 'LoadHowMuch' for the different modes.
--
-- This function implements the core of GHC's @--make@ mode.  It preprocesses,
-- compiles and loads the specified modules, avoiding re-compilation wherever
-- possible.  Depending on the target (see 'DynFlags.hscTarget') compiling
-- and loading may result in files being created on disk.
--
-- Calls the 'defaultWarnErrLogger' after each compiling each module, whether
-- successful or not.
--
-- Throw a 'SourceError' if errors are encountered before the actual
-- compilation starts (e.g., during dependency analysis).  All other errors
-- are reported using the 'defaultWarnErrLogger'.
--
load :: GhcMonad m => LoadHowMuch -> m SuccessFlag
load how_much = do
    mod_graph <- depanal [] False
    load' how_much (Just batchMsg) mod_graph

-- | Generalized version of 'load' which also supports a custom
-- 'Messager' (for reporting progress) and 'ModuleGraph' (generally
-- produced by calling 'depanal'.
load' :: GhcMonad m => LoadHowMuch -> Maybe Messager -> ModuleGraph -> m SuccessFlag
load' how_much mHscMessage mod_graph = do
    modifySession $ \hsc_env -> hsc_env { hsc_mod_graph = mod_graph }
    guessOutputFile
    hsc_env <- getSession
    hpt_old <- liftIO $ hscHPT hsc_env

    let dflags = hsc_dflags hsc_env

    -- The "bad" boot modules are the ones for which we have
    -- B.hs-boot in the module graph, but no B.hs
    -- The downsweep should have ensured this does not happen
    -- (see msDeps)
    let all_home_mods =
          mkUniqSet [ ms_mod_name s
                    | s <- mgModSummaries mod_graph, not (isBootSummary s)]
        bad_boot_mods = [s        | s <- mgModSummaries mod_graph, isBootSummary s,
                                    not (ms_mod_name s `elementOfUniqSet` all_home_mods)]
    ASSERT( null bad_boot_mods ) return ()

    -- check that the module given in HowMuch actually exists, otherwise
    -- topSortModuleGraph will bomb later.
    let checkHowMuch (LoadUpTo m)           = checkMod m
        checkHowMuch (LoadDependenciesOf m) = checkMod m
        checkHowMuch _ = id

        checkMod m and_then
            | m `elementOfUniqSet` all_home_mods = and_then
            | otherwise = do
                    liftIO $ errorMsg dflags (text "no such module:" <+>
                                     quotes (ppr m))
                    return Failed

    checkHowMuch how_much $ do

    -- mg2_with_srcimps drops the hi-boot nodes, returning a
    -- graph with cycles.  Among other things, it is used for
    -- backing out partially complete cycles following a failed
    -- upsweep, and for removing from hpt all the modules
    -- not in strict downwards closure, during calls to compile.
    let mg2_with_srcimps :: [SCC ModSummary]
        mg2_with_srcimps = topSortModuleGraph True mod_graph Nothing

    -- If we can determine that any of the {-# SOURCE #-} imports
    -- are definitely unnecessary, then emit a warning.
    warnUnnecessarySourceImports mg2_with_srcimps

    let
        -- check the stability property for each module.
        stable_mods@(stable_obj,stable_bco)
            = checkStability hpt_old mg2_with_srcimps all_home_mods

        -- prune bits of the HPT which are definitely redundant now,
        -- to save space.
        pruned_hpt = pruneHomePackageTable hpt_old
                            (flattenSCCs mg2_with_srcimps)
                            stable_mods

    liftIO $ debugTraceMsg dflags 2 (text "Stable obj:" <+> ppr stable_obj $$
                            text "Stable BCO:" <+> ppr stable_bco)

    hpt_ref <- liftIO $ newIORef pruned_hpt
    -- before we unload anything, make sure we don't leave an old
    -- interactive context around pointing to dead bindings.
    modifySession $ \hsc_env -> discardIC hsc_env { hsc_HPT = hpt_ref }

    -- Unload any modules which are going to be re-linked this time around.
    let stable_linkables = [ linkable
                           | m <- nonDetEltsUniqSet stable_obj ++
                                  nonDetEltsUniqSet stable_bco,
                             -- It's OK to use nonDetEltsUniqSet here
                             -- because it only affects linking. Besides
                             -- this list only serves as a poor man's set.
                             Just hmi <- [lookupHpt pruned_hpt m],
                             Just linkable <- [hm_linkable hmi] ]

    -- this hsc_env still has the original hpt and interactive context
    liftIO $ unload hsc_env stable_linkables

    -- We could at this point detect cycles which aren't broken by
    -- a source-import, and complain immediately, but it seems better
    -- to let upsweep_mods do this, so at least some useful work gets
    -- done before the upsweep is abandoned.
    --hPutStrLn stderr "after tsort:\n"
    --hPutStrLn stderr (showSDoc (vcat (map ppr mg2)))

    -- Now do the upsweep, calling compile for each module in
    -- turn.  Final result is version 3 of everything.

    -- Topologically sort the module graph, this time including hi-boot
    -- nodes, and possibly just including the portion of the graph
    -- reachable from the module specified in the 2nd argument to load.
    -- This graph should be cycle-free.
    -- If we're restricting the upsweep to a portion of the graph, we
    -- also want to retain everything that is still stable.
    let full_mg :: [SCC ModSummary]
        full_mg    = topSortModuleGraph False mod_graph Nothing

        maybe_top_mod = case how_much of
                            LoadUpTo m           -> Just m
                            LoadDependenciesOf m -> Just m
                            _                    -> Nothing

        partial_mg0 :: [SCC ModSummary]
        partial_mg0 = topSortModuleGraph False mod_graph maybe_top_mod

        -- LoadDependenciesOf m: we want the upsweep to stop just
        -- short of the specified module (unless the specified module
        -- is stable).
        partial_mg
            | LoadDependenciesOf _mod <- how_much
            = ASSERT( case last partial_mg0 of
                        AcyclicSCC ms -> ms_mod_name ms == _mod; _ -> False )
              List.init partial_mg0
            | otherwise
            = partial_mg0

        stable_mg =
            [ AcyclicSCC ms
            | AcyclicSCC ms <- full_mg,
              stable_mod_summary ms ]

        stable_mod_summary ms =
          ms_mod_name ms `elementOfUniqSet` stable_obj ||
          ms_mod_name ms `elementOfUniqSet` stable_bco

        -- the modules from partial_mg that are not also stable
        -- NB. also keep cycles, we need to emit an error message later
        unstable_mg = filter not_stable partial_mg
          where not_stable (CyclicSCC _) = True
                not_stable (AcyclicSCC ms)
                   = not $ stable_mod_summary ms

        -- Load all the stable modules first, before attempting to load
        -- an unstable module (#7231).
        mg = stable_mg ++ unstable_mg
        (comp_graph, mb_cycle) = build_comp_graph  mg
          where
            build_comp_graph  [] = ([], Nothing)
            build_comp_graph  (scc:sccs) = case scc of
              AcyclicSCC m ->
                let (rest,cycle) = build_comp_graph  sccs
                in (m : rest, cycle)
              CyclicSCC ms -> ([], Just ms)
        home_modules_set = Set.fromList [mkBuildModule ms | ms <- comp_graph]
        boot_modules_set =
          mkModuleSet [ms_mod ms | ms <- comp_graph, isBootSummary ms]
        -- The loop that each module will finish. After that module successfully
        -- compiles, this loop is going to get re-typechecked.
        -- The list of all loops in the compilation graph.
        -- NB: For convenience, the last module of each loop (aka the module that
        -- finishes the loop) is prepended to the beginning of the loop.
        comp_graph_loops_map = Map.fromList (go (reverse comp_graph) boot_modules_set)
          where
            remove ms bm
              | isBootSummary ms = delModuleSet bm (ms_mod ms)
              | otherwise = bm
            go [] _ = []
            go mg@(ms:mss) boot_modules
              | Just loop <- getModLoop ms mg (`elemModuleSet` boot_modules) =
                (mkBuildModule ms, loop) : go mss new_boot_modules
              | otherwise = go mss new_boot_modules
              where
                new_boot_modules = remove ms boot_modules
    -- Dealing with module loops
    -- ~~~~~~~~~~~~~~~~~~~~~~~~~
    --
    -- Not only do we have to deal with explicit textual dependencies, we also
    -- have to deal with implicit dependencies introduced by import cycles that
    -- are broken by an hs-boot file. We have to ensure that:
    --
    -- 1. A module that breaks a loop must depend on all the modules in the
    --    loop (transitively or otherwise). This is normally always fulfilled
    --    by the module's textual dependencies except in degenerate loops,
    --    e.g.:
    --
    --    A.hs imports B.hs-boot
    --    B.hs doesn't import A.hs
    --    C.hs imports A.hs, B.hs
    --
    --    In this scenario, getModLoop will detect the module loop [A,B] but
    --    the loop finisher B doesn't depend on A. So we have to explicitly add
    --    A in as a dependency of B when we are compiling B.
    --
    -- 2. A module that depends on a module in an external loop can't proceed
    --    until the entire loop is re-typechecked.
    --
    -- These two invariants have to be maintained to correctly build a
    -- compilation graph with one or more loops.
        mk_tasks =
          [ ( MakeTask this_bm mp
            , mp_cost
            , mt_deps
            )
          | ms <- comp_graph
          , let final_mp = case hscTarget . ms_hspp_opts $ ms of
                  _ -> maxBound
                this_bm = mkBuildModule ms
                textual_deps = Set.intersection home_modules_set $
                  Set.fromList $
                    [ BuildModule mn NotBoot
                    | L _ mn <- ms_home_imps ms
                    ] ++
                    [ BuildModule mn IsBoot
                    | L _ mn <- ms_home_srcimps ms
                    ]
                deps_set = Set.delete this_bm $ fold
                  [ textual_deps
    -- If this module finishes a loop then it must depend on all the other
    -- modules in that loop because the entire module loop is going to be
    -- re-typechecked once this module gets compiled. These extra dependencies
    -- are this module's "internal" loop dependencies, because this module is
    -- inside the loop in question.
                  , Map.foldMapWithKey (\k v -> if (this_bm `Set.member` v) || null (v `Set.intersection` textual_deps) then mempty else Set.singleton k) comp_graph_loops_map
                  ]
                th_needs_codegen x = if isTemplateHaskellOrQQNonBoot ms then MP_CodeGen else x
          , mp <- [minBound .. final_mp]
          , let mt_deps = case mp of
                  MP_Parse -> []
                  MP_Typecheck -> [MakeTask dep_m (th_needs_codegen MP_Simplify) | dep_m <- toList textual_deps ] `mappend` [MakeTask dep_m (th_needs_codegen MP_Simplify) | dep_m <- toList deps_set] `mappend` [MakeTask this_bm MP_Parse]
                  MP_Simplify ->
                    [MakeTask this_bm MP_Typecheck] `mappend`
                    [MakeTask dep_m MP_Typecheck
                    | dep_m <- toList $ foldMap (\v -> if (this_bm `Set.member` v)  then v else mempty) comp_graph_loops_map
                    ]
                  MP_CodeGen ->
                    [MakeTask this_bm MP_Simplify]
                -- These are entirely made up
                mp_cost = makeValue (case mp of
                  MP_Parse -> 100
                  MP_Typecheck -> 200
                  MP_Simplify -> 500
                  MP_CodeGen -> 1000)
          ]
        make_queue = mkMakeQueue mk_tasks

    -- clean up between compilations
    let cleanup = cleanCurrentModuleTempFiles . hsc_dflags
    liftIO $ debugTraceMsg dflags 2 (hang (text "Ready for upsweep")
                               2 (ppr mg))

    liftIO $ writeIORef hpt_ref $! emptyHomePackageTable

    (upsweep_ok, modsUpswept)
       <- do
        (upsweep_ok, modsUpswept) <- parUpsweep mHscMessage pruned_hpt stable_mods cleanup comp_graph comp_graph_loops_map make_queue
        -- Handle any cycle in the original compilation graph and return the result
        -- of the upsweep.
        case mb_cycle of
          Just mss -> do
              liftIO $ fatalErrorMsg dflags (cyclicModuleErr mss)
              return (Failed, modsUpswept)
          Nothing  -> do
              return (upsweep_ok, modsUpswept)

    -- Make modsDone be the summaries for each home module now
    -- available; this should equal the domain of hpt.
    -- Get in in a roughly top .. bottom order (hence reverse).

    let modsDone = reverse modsUpswept

    -- Try and do linking in some form, depending on whether the
    -- upsweep was completely or only partially successful.

    if succeeded upsweep_ok

     then
       -- Easy; just relink it all.
       do liftIO $ debugTraceMsg dflags 2 (text "Upsweep completely successful.")
          hpt <- liftIO $ readIORef hpt_ref

          -- Clean up after ourselves
          liftIO $ cleanCurrentModuleTempFiles dflags

          -- Issue a warning for the confusing case where the user
          -- said '-o foo' but we're not going to do any linking.
          -- We attempt linking if either (a) one of the modules is
          -- called Main, or (b) the user said -no-hs-main, indicating
          -- that main() is going to come from somewhere else.
          --
          let ofile = outputFile dflags
          let no_hs_main = gopt Opt_NoHsMain dflags
          let
            main_mod = mainModIs dflags
            a_root_is_Main = mgElemModule mod_graph main_mod
            do_linking = a_root_is_Main || no_hs_main || ghcLink dflags == LinkDynLib || ghcLink dflags == LinkStaticLib

          -- link everything together
          linkresult <- liftIO $ link (ghcLink dflags) dflags do_linking hpt

          if ghcLink dflags == LinkBinary && isJust ofile && not do_linking
             then do
                liftIO $ errorMsg dflags $ text
                   ("output was redirected with -o, " ++
                    "but no output will be generated\n" ++
                    "because there is no " ++
                    moduleNameString (moduleName main_mod) ++ " module.")
                -- This should be an error, not a warning (#10895).
                loadFinish Failed linkresult
             else
                loadFinish Succeeded linkresult

     else
       -- Tricky.  We need to back out the effects of compiling any
       -- half-done cycles, both so as to clean up the top level envs
       -- and to avoid telling the interactive linker to link them.
       do liftIO $ debugTraceMsg dflags 2 (text "Upsweep partially successful.")

          let modsDone_names
                 = map ms_mod modsDone
          let mods_to_zap_names
                 = findPartiallyCompletedCycles modsDone_names
                      mg2_with_srcimps
          let (mods_to_clean, mods_to_keep) =
                partition ((`Set.member` mods_to_zap_names).ms_mod) modsDone
          hpt <- liftIO $ readIORef hpt_ref

              -- We must change the lifetime to TFL_CurrentModule for any temp
              -- file created for an element of mod_to_clean during the upsweep.
              -- These include preprocessed files and object files for loaded
              -- modules.
          let unneeded_temps = concat
                [ms_hspp_file : object_files
                | ModSummary{ms_mod, ms_hspp_file} <- mods_to_clean
                , let object_files = maybe [] linkableObjs $
                        lookupHpt hpt (moduleName ms_mod)
                        >>= hm_linkable
                ]
          -- Clean up after ourselves
          liftIO $
            changeTempFilesLifetime dflags TFL_CurrentModule unneeded_temps
          liftIO $ cleanCurrentModuleTempFiles dflags

          let hpt2 = retainInTopLevelEnvs (map ms_mod_name mods_to_keep)
                                          hpt

          liftIO $ writeIORef hpt_ref $! hpt2

          -- there should be no Nothings where linkables should be, now
          let just_linkables =
                    isNoLink (ghcLink dflags)
                 || allHpt (isJust.hm_linkable)
                        (filterHpt ((== HsSrcFile).mi_hsc_src.hm_iface)
                                hpt2)
          ASSERT( just_linkables ) do

          -- Link everything together
          linkresult <- liftIO $ link (ghcLink dflags) dflags False hpt2

          loadFinish Failed linkresult


-- | Finish up after a load.
loadFinish :: GhcMonad m => SuccessFlag -> SuccessFlag -> m SuccessFlag

-- If the link failed, unload everything and return.
loadFinish _all_ok Failed
  = do hsc_env <- getSession
       liftIO $ unload hsc_env []
       liftIO (discardProg hsc_env) >>= setSession
       return Failed

-- Empty the interactive context and set the module context to the topmost
-- newly loaded module, or the Prelude if none were loaded.
loadFinish all_ok Succeeded
  = do modifySession discardIC
       return all_ok


-- | Forget the current program, but retain the persistent info in HscEnv
discardProg :: HscEnv -> IO HscEnv
discardProg hsc_env
  = do
  new_hpt <- newIORef emptyHomePackageTable
  return $ discardIC $ hsc_env
    { hsc_mod_graph = emptyMG
    , hsc_HPT = new_hpt
    }

-- | Discard the contents of the InteractiveContext, but keep the DynFlags.
-- It will also keep ic_int_print and ic_monad if their names are from
-- external packages.
discardIC :: HscEnv -> HscEnv
discardIC hsc_env
  = hsc_env { hsc_IC = empty_ic { ic_int_print = new_ic_int_print
                                , ic_monad = new_ic_monad } }
  where
  -- Force the new values for ic_int_print and ic_monad to avoid leaking old_ic
  !new_ic_int_print = keep_external_name ic_int_print
  !new_ic_monad = keep_external_name ic_monad
  dflags = ic_dflags old_ic
  old_ic = hsc_IC hsc_env
  empty_ic = emptyInteractiveContext dflags
  keep_external_name ic_name
    | nameIsFromExternalPackage this_pkg old_name = old_name
    | otherwise = ic_name empty_ic
    where
    this_pkg = thisPackage dflags
    old_name = ic_name old_ic

-- | If there is no -o option, guess the name of target executable
-- by using top-level source file name as a base.
guessOutputFile :: GhcMonad m => m ()
guessOutputFile = modifySession $ \env ->
    let dflags = hsc_dflags env
        -- Force mod_graph to avoid leaking env
        !mod_graph = hsc_mod_graph env
        mainModuleSrcPath :: Maybe String
        mainModuleSrcPath = do
            ms <- mgLookupModule mod_graph (mainModIs dflags)
            ml_hs_file (ms_location ms)
        name = fmap dropExtension mainModuleSrcPath

        name_exe = do
#if defined(mingw32_HOST_OS)
          -- we must add the .exe extension unconditionally here, otherwise
          -- when name has an extension of its own, the .exe extension will
          -- not be added by DriverPipeline.exeFileName.  See #2248
          name' <- fmap (<.> "exe") name
#else
          name' <- name
#endif
          mainModuleSrcPath' <- mainModuleSrcPath
          -- #9930: don't clobber input files (unless they ask for it)
          if name' == mainModuleSrcPath'
            then throwGhcException . UsageError $
                 "default output name would overwrite the input file; " ++
                 "must specify -o explicitly"
            else Just name'
    in
    case outputFile dflags of
        Just _ -> env
        Nothing -> env { hsc_dflags = dflags { outputFile = name_exe } }

-- -----------------------------------------------------------------------------
--
-- | Prune the HomePackageTable
--
-- Before doing an upsweep, we can throw away:
--
--   - For non-stable modules:
--      - all ModDetails, all linked code
--   - all unlinked code that is out of date with respect to
--     the source file
--
-- This is VERY IMPORTANT otherwise we'll end up requiring 2x the
-- space at the end of the upsweep, because the topmost ModDetails of the
-- old HPT holds on to the entire type environment from the previous
-- compilation.
pruneHomePackageTable :: HomePackageTable
                      -> [ModSummary]
                      -> StableModules
                      -> HomePackageTable
pruneHomePackageTable hpt summ (stable_obj, stable_bco)
  = mapHpt prune hpt
  where prune hmi
          | is_stable modl = hmi'
          | otherwise      = hmi'{ hm_details = emptyModDetails }
          where
           modl = moduleName (mi_module (hm_iface hmi))
           hmi' | Just l <- hm_linkable hmi, linkableTime l < ms_hs_date ms
                = hmi{ hm_linkable = Nothing }
                | otherwise
                = hmi
                where ms = expectJust "prune" (lookupUFM ms_map modl)

        ms_map = listToUFM [(ms_mod_name ms, ms) | ms <- summ]

        is_stable m =
          m `elementOfUniqSet` stable_obj ||
          m `elementOfUniqSet` stable_bco

-- -----------------------------------------------------------------------------
--
-- | Return (names of) all those in modsDone who are part of a cycle as defined
-- by theGraph.
findPartiallyCompletedCycles :: [Module] -> [SCC ModSummary] -> Set.Set Module
findPartiallyCompletedCycles modsDone theGraph
   = Set.unions
       [mods_in_this_cycle
       | CyclicSCC vs <- theGraph  -- Acyclic? Not interesting.
       , let names_in_this_cycle = Set.fromList (map ms_mod vs)
             mods_in_this_cycle =
                    Set.intersection (Set.fromList modsDone) names_in_this_cycle
         -- If size mods_in_this_cycle == size names_in_this_cycle,
         -- then this cycle has already been completed and we're not
         -- interested.
       , Set.size mods_in_this_cycle < Set.size names_in_this_cycle]


-- ---------------------------------------------------------------------------
--
-- | Unloading
unload :: HscEnv -> [Linkable] -> IO ()
unload hsc_env stable_linkables -- Unload everthing *except* 'stable_linkables'
  = case ghcLink (hsc_dflags hsc_env) of
        LinkInMemory -> Linker.unload hsc_env stable_linkables
        _other -> return ()

-- -----------------------------------------------------------------------------
{- |

  Stability tells us which modules definitely do not need to be recompiled.
  There are two main reasons for having stability:

   - avoid doing a complete upsweep of the module graph in GHCi when
     modules near the bottom of the tree have not changed.

   - to tell GHCi when it can load object code: we can only load object code
     for a module when we also load object code fo  all of the imports of the
     module.  So we need to know that we will definitely not be recompiling
     any of these modules, and we can use the object code.

  The stability check is as follows.  Both stableObject and
  stableBCO are used during the upsweep phase later.

@
  stable m = stableObject m || stableBCO m

  stableObject m =
        all stableObject (imports m)
        && old linkable does not exist, or is == on-disk .o
        && date(on-disk .o) > date(.hs)

  stableBCO m =
        all stable (imports m)
        && date(BCO) > date(.hs)
@

  These properties embody the following ideas:

    - if a module is stable, then:

        - if it has been compiled in a previous pass (present in HPT)
          then it does not need to be compiled or re-linked.

        - if it has not been compiled in a previous pass,
          then we only need to read its .hi file from disk and
          link it to produce a 'ModDetails'.

    - if a modules is not stable, we will definitely be at least
      re-linking, and possibly re-compiling it during the 'upsweep'.
      All non-stable modules can (and should) therefore be unlinked
      before the 'upsweep'.

    - Note that objects are only considered stable if they only depend
      on other objects.  We can't link object code against byte code.

    - Note that even if an object is stable, we may end up recompiling
      if the interface is out of date because an *external* interface
      has changed.  The current code in GhcMake handles this case
      fairly poorly, so be careful.
-}

type StableModules =
  ( UniqSet ModuleName  -- stableObject
  , UniqSet ModuleName  -- stableBCO
  )


checkStability
        :: HomePackageTable   -- HPT from last compilation
        -> [SCC ModSummary]   -- current module graph (cyclic)
        -> UniqSet ModuleName -- all home modules
        -> StableModules

checkStability hpt sccs all_home_mods =
  foldl checkSCC (emptyUniqSet, emptyUniqSet) sccs
  where
   checkSCC :: StableModules -> SCC ModSummary -> StableModules
   checkSCC (stable_obj, stable_bco) scc0
     | stableObjects = (addListToUniqSet stable_obj scc_mods, stable_bco)
     | stableBCOs    = (stable_obj, addListToUniqSet stable_bco scc_mods)
     | otherwise     = (stable_obj, stable_bco)
     where
        scc = flattenSCC scc0
        scc_mods = map ms_mod_name scc
        home_module m =
          m `elementOfUniqSet` all_home_mods && m `notElem` scc_mods

        scc_allimps = nub (filter home_module (concatMap ms_home_allimps scc))
            -- all imports outside the current SCC, but in the home pkg

        stable_obj_imps = map (`elementOfUniqSet` stable_obj) scc_allimps
        stable_bco_imps = map (`elementOfUniqSet` stable_bco) scc_allimps

        stableObjects =
           and stable_obj_imps
           && all object_ok scc

        stableBCOs =
           and (zipWith (||) stable_obj_imps stable_bco_imps)
           && all bco_ok scc

        object_ok ms
          | gopt Opt_ForceRecomp (ms_hspp_opts ms) = False
          | Just t <- ms_obj_date ms  =  t >= ms_hs_date ms
                                         && same_as_prev t
          | otherwise = False
          where
             same_as_prev t = case lookupHpt hpt (ms_mod_name ms) of
                                Just hmi  | Just l <- hm_linkable hmi
                                 -> isObjectLinkable l && t == linkableTime l
                                _other  -> True
                -- why '>=' rather than '>' above?  If the filesystem stores
                -- times to the nearset second, we may occasionally find that
                -- the object & source have the same modification time,
                -- especially if the source was automatically generated
                -- and compiled.  Using >= is slightly unsafe, but it matches
                -- make's behaviour.
                --
                -- But see #5527, where someone ran into this and it caused
                -- a problem.

        bco_ok ms
          | gopt Opt_ForceRecomp (ms_hspp_opts ms) = False
          | otherwise = case lookupHpt hpt (ms_mod_name ms) of
                Just hmi  | Just l <- hm_linkable hmi ->
                        not (isObjectLinkable l) &&
                        linkableTime l >= ms_hs_date ms
                _other  -> False

{- Parallel Upsweep
 -
 - The parallel upsweep attempts to concurrently compile the modules in the
 - compilation graph using multiple Haskell threads.
 -
 - The Algorithm
 -
 - A Haskell thread is spawned for each module in the module graph, waiting for
 - its direct dependencies to finish building before it itself begins to build.
 -
 - Each module is associated with an initially empty MVar that stores the
 - result of that particular module's compile. If the compile succeeded, then
 - the HscEnv (synchronized by an MVar) is updated with the fresh HMI of that
 - module, and the module's HMI is deleted from the old HPT (synchronized by an
 - IORef) to save space.
 -
 - Instead of immediately outputting messages to the standard handles, all
 - compilation output is deferred to a per-module TQueue. A QSem is used to
 - limit the number of workers that are compiling simultaneously.
 -
 - Meanwhile, the main thread sequentially loops over all the modules in the
 - module graph, outputting the messages stored in each module's TQueue.
-}

-- | Tests if an 'HscSource' is a boot file, primarily for constructing
-- elements of 'BuildModule'.
hscSourceToIsBoot :: HscSource -> IsBoot
hscSourceToIsBoot HsBootFile = IsBoot
hscSourceToIsBoot _ = NotBoot

mkBuildModule :: ModSummary -> BuildModule
mkBuildModule mod_sum = BuildModule (ms_mod_name mod_sum) (hscSourceToIsBoot . ms_hsc_src $ mod_sum)

data CompilationCancelled = CompilationCancelled
  deriving (Show, Eq, Typeable)

instance Exception CompilationCancelled

-- | The entry point to the parallel upsweep.
--
-- See also the simpler, sequential 'upsweep'.
parUpsweep
    :: GhcMonad m
    => Maybe Messager
    -> HomePackageTable
    -> StableModules
    -> (HscEnv -> IO ())
    -> [ModSummary]
    -> Map BuildModule (Set BuildModule)
    -> MakeQueue
    -> m (SuccessFlag,
          [ModSummary])
parUpsweep mHscMessage old_hpt stable_mods cleanup comp_graph graph_loops make_queue =
  -- pprTrace "parUpsweep" (vcat
  --     [text "graph_loops:" <+> ppr graph_loops
  --     , text "comp_graph:" <+> ppr comp_graph
  --     ]) $
  do
    hsc_env0 <- getSession
    let dflags = hsc_dflags hsc_env0

    -- The old HPT is used for recompilation checking in upsweep_mod. When a
    -- module successfully gets compiled, its HMI is pruned from the old HPT.
    old_hpt_var <- liftIO $ newIORef old_hpt

    num_processors <- liftIO getNumProcessors

    let n_jobs = fromMaybe num_processors . parMakeCount $ dflags
        updNumCapabilities = liftIO $ do
            n_capabilities <- getNumCapabilities
            -- Setting number of capabilities more than
            -- CPU count usually leads to high userspace
            -- lock contention. Trac #9221
            let n_caps = min n_jobs num_processors
            unless (n_capabilities /= 1) $ setNumCapabilities n_caps
            return n_capabilities
        -- Reset the number of capabilities once the upsweep ends.
        resetNumCapabilities orig_n = liftIO $ setNumCapabilities orig_n

    pus_module_data <- liftIO $ fmap Map.fromList $ for comp_graph $ \ms -> do
      mvar <- newEmptyMVar
      return $ (mkBuildModule ms, BuildModuleState Seq.empty $ WaitingToStart MP_Parse mvar)
    pum_chan <- liftIO newChan

    let pus = ParUpsweepState
          { pus_module_data
          , pus_free_jobs = n_jobs
          , pus_make_queue = make_queue}
        home_modules_set = Set.fromList [mkBuildModule ms | ms <- comp_graph]
        HscYield
          { yieldParsedSource = yieldParsedSource'
          , yieldTypecheckedInterface = yieldTypecheckedInterface'
          , yieldSimplifiedInterface = yieldSimplifiedInterface'
          } = hsc_yield hsc_env0
        await_pu_response f = do
          continue_mvar <- newEmptyMVar
          writeChan pum_chan (f continue_mvar)
          take_mvar_and_continue continue_mvar
        await_modules bm mp bms = await_pu_response $
          PUM_AdHocWait bm infiniteMakeValue [MakeTask bm mp | bm <- toList bms]
        take_mvar_and_continue mv =
          takeMVar mv >>= \continue ->
            unless continue $ throwIO CompilationCancelled
        yieldParsedSource hsc_env mod_sum x = do
          yieldParsedSource' hsc_env mod_sum x
          await_pu_response $ PUM_Parsed $ mkBuildModule mod_sum
        yieldTypecheckedInterface hsc_env mod_sum iface mb_details = do
          hmi <- yieldTypecheckedInterface' hsc_env mod_sum iface mb_details
          await_pu_response $ PUM_Typechecked $ mkBuildModule mod_sum
          return hmi
        yieldSimplifiedInterface hsc_env mod_sum iface mb_details = do
          hmi <- yieldSimplifiedInterface' hsc_env mod_sum iface mb_details
          let bm = mkBuildModule mod_sum
          for_ (Map.lookup bm graph_loops) $ \bms -> do
            typecheckLoop
              (hsc_dflags hsc_env)
              hsc_env
              (toList . Set.map buildModuleModuleName $ bms)
          await_pu_response $ PUM_Simplified bm
          return hmi
        awaitDependencyInterfaces _hsc_env mod_sum =
          await_modules (mkBuildModule mod_sum) MP_Typecheck
          [ bm
          | bm <-
            [ BuildModule mn NotBoot | L _ mn <- ms_home_imps mod_sum]
            ++ [ BuildModule mn IsBoot | L _ mn <- ms_home_srcimps mod_sum]
          , bm `Set.member` home_modules_set
          ]
    gbracket updNumCapabilities resetNumCapabilities $ \_ -> do

    -- Build the compilation graph out of the list of SCCs. Module cycles are
    -- handled at the very end, after some useful work gets done. Note that
    -- this list is topologically sorted (by virtue of 'sccs' being sorted so).

    liftIO $ label_self "main --make thread"
    -- For each module in the module graph, spawn a worker thread that will
    -- compile this module.
    let { spawnWorkers = forM (zip [1..] comp_graph) $ \(mod_idx, mod_sum) ->
            forkIOWithUnmask $ \unmask -> do
                liftIO $ label_self $ unwords
                    [ "worker --make thread"
                    , "for module"
                    , show (moduleNameString (ms_mod_name mod_sum))
                    , "number"
                    , show mod_idx
                    ]
                type_env_var <- liftIO $ newIORef emptyNameEnv
                lcl_files_to_clean <- newIORef emptyFilesToClean
                -- Replace the default log_action with one that writes each
                -- message to the module's log_queue. The main thread will
                -- deal with synchronously printing these messages.
                --
                -- Use a local filesToClean var so that we can clean up
                -- intermediate files in a timely fashion (as soon as
                -- compilation for that module is finished) without having to
                -- worry about accidentally deleting a simultaneous compile's
                -- important files.
                let parLogAction dflags wr sev ss ps d =
                      writeChan pum_chan $ PUM_Log bm $
                       LogData dflags wr sev ss ps d
                    lcl_dflags = dflags { log_action = parLogAction
                                        , filesToClean = lcl_files_to_clean }
                    hsc_env = hsc_env0
                      {hsc_dflags = lcl_dflags
                      , hsc_yield = HscYield {..}
                      , hsc_type_env_var = Just (ms_mod lcl_mod, type_env_var)
                      }
                    bm = mkBuildModule mod_sum
                    lcl_mod = mod_sum
                      { ms_hspp_opts = (ms_hspp_opts mod_sum)
                        { log_action = log_action lcl_dflags
                        , filesToClean = filesToClean lcl_dflags
                        }
                      }

                -- Unmask asynchronous exceptions and perform the thread-local
                m_res <- try $ unmask $ do
                        liftIO $ take_mvar_and_continue $
                          (\(BuildModuleState _ (WaitingToStart _ x)) -> x) $ pus_module_data Map.! bm
                        -- Re-typecheck the loop
                        -- This is necessary to make sure the knot is tied when
                        -- we close a recursive module loop, see bug #12035.
                        for_ (Map.lookup bm graph_loops) $ \bms -> do
                          await_modules bm MP_Typecheck (Set.delete bm bms)
                          typecheckLoop
                            lcl_dflags
                            hsc_env
                            (toList . Set.map buildModuleModuleName $ bms)
                        parUpsweep_one hsc_env lcl_mod
                                       mHscMessage cleanup
                                       old_hpt_var
                                       stable_mods
                                       mod_idx (length comp_graph)
                res <- case m_res of
                    Right flag -> return flag
                    Left exc -> do
                        -- Don't print ThreadKilled exceptions: they are used
                        -- to kill the worker thread in the event of a user
                        -- interrupt, and the user doesn't have to be informed
                        -- about that.
                        when
                         ( fromException exc /= Just ThreadKilled
                         && fromException exc /= Just CompilationCancelled
                         )
                             (errorMsg lcl_dflags (text (show exc)))
                        return Failed
                writeChan pum_chan $ PUM_Finished bm res

                -- Add the remaining files that weren't cleaned up to the
                -- global filesToClean ref, for cleanup later.
                FilesToClean
                  { ftcCurrentModule = cm_files
                  , ftcGhcSession = gs_files
                  } <- readIORef (filesToClean lcl_dflags)
                addFilesToClean dflags TFL_CurrentModule $ Set.toList cm_files
                addFilesToClean dflags TFL_GhcSession $ Set.toList gs_files

        -- Kill all the workers, masking interrupts (since killThread is
        -- interruptible). XXX: This is not ideal.
        ; killWorkers = uninterruptibleMask_ . mapM_ killThread }


    -- Spawn the workers, making sure to kill them later. Collect the results
    -- of each compile.
    results <- liftIO $ bracket spawnWorkers killWorkers $ \_ ->
        let go = for comp_graph $ \ms -> do
              let bm = mkBuildModule ms
              sf <- monitorChanUntilModuleComplete (log_action dflags) pum_chan bm
              if succeeded sf
              then return (Just ms)
              else return Nothing
        in runUpsweepM go pus

    _ <- liftIO $ runHsc hsc_env0 $ mapM_ (ioMsgMaybe . tcRnCheckUnitId hsc_env0) (unitIdsToCheck dflags)
    -- Collect and return the ModSummaries of all the successful compiles.
    -- NB: Reverse this list to maintain output parity with the sequential upsweep.
    let ok_results = reverse (catMaybes results)
    let success_flag = successIf (all isJust results)
    return (success_flag, ok_results)

-- The interruptible subset of the worker threads' work.
parUpsweep_one
    :: HscEnv
    -> ModSummary
    -> Maybe Messager
    -- ^ The messager
    -> (HscEnv -> IO ())
    -- ^ The callback for cleaning up intermediate files
    -> IORef HomePackageTable
    -- ^ The old HPT
    -> StableModules
    -- ^ Sets of stable objects and BCOs
    -> Int
    -- ^ The index of this module
    -> Int
    -- ^ The total number of modules
    -> IO SuccessFlag
    -- ^ The result of this compile
parUpsweep_one lcl_hsc_env mod mHscMessage cleanup
               old_hpt_var stable_mods mod_index num_mods = do
        let lcl_dflags = hsc_dflags lcl_hsc_env
        -- Any hsc_env at this point is OK to use since we only really require
        -- that the HPT contains the HMIs of our dependencies.
        old_hpt <- readIORef old_hpt_var

        let logger err = printBagOfErrors lcl_dflags (srcErrorMessages err)

        mb_mod_info <-
            handleSourceError (\err -> do logger err; return Nothing) $ do
                -- Compile the module.
                mod_info <- upsweep_mod lcl_hsc_env mHscMessage old_hpt
                                        stable_mods mod mod_index num_mods
                return (Just mod_info)

        case mb_mod_info of
            Nothing -> return Failed
            Just mod_info -> do
                let this_mod = ms_mod_name mod

                -- Prune the old HPT unless this is an hs-boot module.
                unless (isBootSummary mod) $
                    atomicModifyIORef' old_hpt_var $ \old_hpt ->
                        (delFromHpt old_hpt this_mod, ())

                -- This adds the linkables to the hpt
                atomicModifyIORef' (hsc_HPT lcl_hsc_env) $
                  \hpt -> (addToHpt hpt this_mod mod_info, ())

                -- Add any necessary entries to the static pointer
                -- table. See Note [Grand plan for static forms] in
                -- StaticPtrTable.
                when (hscTarget lcl_dflags == HscInterpreted) $
                    liftIO $ hscAddSptEntries lcl_hsc_env
                                 [ spt
                                 | Just linkable <- pure $ hm_linkable mod_info
                                 , unlinked <- linkableUnlinked linkable
                                 , BCOs _ spts <- pure unlinked
                                 , spt <- spts
                                 ]

                -- Clean up any intermediate files.
                cleanup lcl_hsc_env
                return Succeeded

  where


unitIdsToCheck :: DynFlags -> [UnitId]
unitIdsToCheck dflags =
  nubSort $ concatMap goUnitId (explicitPackages (pkgState dflags))
 where
  goUnitId uid =
    case splitUnitIdInsts uid of
      (_, Just indef) ->
        let insts = indefUnitIdInsts indef
        in uid : concatMap (goUnitId . moduleUnitId . snd) insts
      _ -> []

maybeGetIfaceDate :: DynFlags -> ModLocation -> IO (Maybe UTCTime)
maybeGetIfaceDate dflags location
 | writeInterfaceOnlyMode dflags
    -- Minor optimization: it should be harmless to check the hi file location
    -- always, but it's better to avoid hitting the filesystem if possible.
    = modificationTimeIfExists (ml_hi_file location)
 | otherwise
    = return Nothing

-- | Compile a single module.  Always produce a Linkable for it if
-- successful.  If no compilation happened, return the old Linkable.
upsweep_mod :: HscEnv
            -> Maybe Messager
            -> HomePackageTable
            -> StableModules
            -> ModSummary
            -> Int  -- index of module
            -> Int  -- total number of modules
            -> IO HomeModInfo
upsweep_mod hsc_env mHscMessage old_hpt (stable_obj, stable_bco) summary mod_index nmods
   =    let
            this_mod_name = ms_mod_name summary
            this_mod    = ms_mod summary
            mb_obj_date = ms_obj_date summary
            mb_if_date  = ms_iface_date summary
            obj_fn      = ml_obj_file (ms_location summary)
            hs_date     = ms_hs_date summary

            is_stable_obj = this_mod_name `elementOfUniqSet` stable_obj
            is_stable_bco = this_mod_name `elementOfUniqSet` stable_bco

            old_hmi = lookupHpt old_hpt this_mod_name

            -- We're using the dflags for this module now, obtained by
            -- applying any options in its LANGUAGE & OPTIONS_GHC pragmas.
            dflags = ms_hspp_opts summary
            prevailing_target = hscTarget (hsc_dflags hsc_env)
            local_target      = hscTarget dflags

            -- If OPTIONS_GHC contains -fasm or -fllvm, be careful that
            -- we don't do anything dodgy: these should only work to change
            -- from -fllvm to -fasm and vice-versa, or away from -fno-code,
            -- otherwise we could end up trying to link object code to byte
            -- code.
            target = if prevailing_target /= local_target
                        && (not (isObjectTarget prevailing_target)
                            || not (isObjectTarget local_target))
                        && not (prevailing_target == HscNothing)
                        then prevailing_target
                        else local_target

            -- store the corrected hscTarget into the summary
            summary' = summary{ ms_hspp_opts = dflags { hscTarget = target } }

            -- The old interface is ok if
            --  a) we're compiling a source file, and the old HPT
            --     entry is for a source file
            --  b) we're compiling a hs-boot file
            -- Case (b) allows an hs-boot file to get the interface of its
            -- real source file on the second iteration of the compilation
            -- manager, but that does no harm.  Otherwise the hs-boot file
            -- will always be recompiled

            mb_old_iface
                = case old_hmi of
                     Nothing                              -> Nothing
                     Just hm_info | isBootSummary summary -> Just iface
                                  | not (mi_boot iface)   -> Just iface
                                  | otherwise             -> Nothing
                                   where
                                     iface = hm_iface hm_info

            compile_it :: Maybe Linkable -> SourceModified -> IO HomeModInfo
            compile_it  mb_linkable src_modified =
                  compileOne' Nothing mHscMessage hsc_env summary' mod_index nmods
                             mb_old_iface mb_linkable src_modified

            compile_it_discard_iface :: Maybe Linkable -> SourceModified
                                     -> IO HomeModInfo
            compile_it_discard_iface mb_linkable  src_modified =
                  compileOne' Nothing mHscMessage hsc_env summary' mod_index nmods
                             Nothing mb_linkable src_modified

            -- With the HscNothing target we create empty linkables to avoid
            -- recompilation.  We have to detect these to recompile anyway if
            -- the target changed since the last compile.
            is_fake_linkable
               | Just hmi <- old_hmi, Just l <- hm_linkable hmi =
                  null (linkableUnlinked l)
               | otherwise =
                   -- we have no linkable, so it cannot be fake
                   False

            implies False _ = True
            implies True x  = x

        in
        case () of
         _
                -- Regardless of whether we're generating object code or
                -- byte code, we can always use an existing object file
                -- if it is *stable* (see checkStability).
          | is_stable_obj, Just hmi <- old_hmi -> do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "skipping stable obj mod:" <+> ppr this_mod_name)
                return hmi
                -- object is stable, and we have an entry in the
                -- old HPT: nothing to do

          | is_stable_obj, isNothing old_hmi -> do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "compiling stable on-disk mod:" <+> ppr this_mod_name)
                linkable <- liftIO $ findObjectLinkable this_mod obj_fn
                              (expectJust "upsweep1" mb_obj_date)
                compile_it (Just linkable) SourceUnmodifiedAndStable
                -- object is stable, but we need to load the interface
                -- off disk to make a HMI.

          | not (isObjectTarget target), is_stable_bco,
            (target /= HscNothing) `implies` not is_fake_linkable ->
                ASSERT(isJust old_hmi) -- must be in the old_hpt
                let Just hmi = old_hmi in do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "skipping stable BCO mod:" <+> ppr this_mod_name)
                return hmi
                -- BCO is stable: nothing to do

          | not (isObjectTarget target),
            Just hmi <- old_hmi,
            Just l <- hm_linkable hmi,
            not (isObjectLinkable l),
            (target /= HscNothing) `implies` not is_fake_linkable,
            linkableTime l >= ms_hs_date summary -> do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "compiling non-stable BCO mod:" <+> ppr this_mod_name)
                compile_it (Just l) SourceUnmodified
                -- we have an old BCO that is up to date with respect
                -- to the source: do a recompilation check as normal.

          -- When generating object code, if there's an up-to-date
          -- object file on the disk, then we can use it.
          -- However, if the object file is new (compared to any
          -- linkable we had from a previous compilation), then we
          -- must discard any in-memory interface, because this
          -- means the user has compiled the source file
          -- separately and generated a new interface, that we must
          -- read from the disk.
          --
          | isObjectTarget target,
            Just obj_date <- mb_obj_date,
            obj_date >= hs_date -> do
                case old_hmi of
                  Just hmi
                    | Just l <- hm_linkable hmi,
                      isObjectLinkable l && linkableTime l == obj_date -> do
                          liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                                     (text "compiling mod with new on-disk obj:" <+> ppr this_mod_name)
                          compile_it (Just l) SourceUnmodified
                  _otherwise -> do
                          liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                                     (text "compiling mod with new on-disk obj2:" <+> ppr this_mod_name)
                          linkable <- liftIO $ findObjectLinkable this_mod obj_fn obj_date
                          compile_it_discard_iface (Just linkable) SourceUnmodified

          -- See Note [Recompilation checking in -fno-code mode]
          | writeInterfaceOnlyMode dflags,
            Just if_date <- mb_if_date,
            if_date >= hs_date -> do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "skipping tc'd mod:" <+> ppr this_mod_name)
                compile_it Nothing SourceUnmodified

         _otherwise -> do
                liftIO $ debugTraceMsg (hsc_dflags hsc_env) 5
                           (text "compiling mod:" <+> ppr this_mod_name)
                compile_it Nothing SourceModified


{- Note [-fno-code mode]
~~~~~~~~~~~~~~~~~~~~~~~~
GHC offers the flag -fno-code for the purpose of parsing and typechecking a
program without generating object files. This is intended to be used by tooling
and IDEs to provide quick feedback on any parser or type errors as cheaply as
possible.

When GHC is invoked with -fno-code no object files or linked output will be
generated. As many errors and warnings as possible will be generated, as if
-fno-code had not been passed. The session DynFlags will have
hscTarget == HscNothing.

-fwrite-interface
~~~~~~~~~~~~~~~~
Whether interface files are generated in -fno-code mode is controlled by the
-fwrite-interface flag. The -fwrite-interface flag is a no-op if -fno-code is
not also passed. Recompilation avoidance requires interface files, so passing
-fno-code without -fwrite-interface should be avoided. If -fno-code were
re-implemented today, -fwrite-interface would be discarded and it would be
considered always on; this behaviour is as it is for backwards compatibility.

================================================================
IN SUMMARY: ALWAYS PASS -fno-code AND -fwrite-interface TOGETHER
================================================================

Template Haskell
~~~~~~~~~~~~~~~~
A module using template haskell may invoke an imported function from inside a
splice. This will cause the type-checker to attempt to execute that code, which
would fail if no object files had been generated. See #8025. To rectify this,
during the downsweep we patch the DynFlags in the ModSummary of any home module
that is imported by a module that uses template haskell, to generate object
code.

The flavour of generated object code is chosen by defaultObjectTarget for the
target platform. It would likely be faster to generate bytecode, but this is not
supported on all platforms(?Please Confirm?), and does not support the entirety
of GHC haskell. See #1257.

The object files (and interface files if -fwrite-interface is disabled) produced
for template haskell are written to temporary files.

Note that since template haskell can run arbitrary IO actions, -fno-code mode
is no more secure than running without it.

Potential TODOS:
~~~~~
* Remove -fwrite-interface and have interface files always written in -fno-code
  mode
* Both .o and .dyn_o files are generated for template haskell, but we only need
  .dyn_o. Fix it.
* In make mode, a message like
  Compiling A (A.hs, /tmp/ghc_123.o)
  is shown if downsweep enabled object code generation for A. Perhaps we should
  show "nothing" or "temporary object file" instead. Note that one
  can currently use -keep-tmp-files and inspect the generated file with the
  current behaviour.
* Offer a -no-codedir command line option, and write what were temporary
  object files there. This would speed up recompilation.
* Use existing object files (if they are up to date) instead of always
  generating temporary ones.
-}

-- Note [Recompilation checking in -fno-code mode]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- If we are compiling with -fno-code -fwrite-interface, there won't
-- be any object code that we can compare against, nor should there
-- be: we're *just* generating interface files.  In this case, we
-- want to check if the interface file is new, in lieu of the object
-- file.  See also Trac #9243.

-- Filter modules in the HPT
retainInTopLevelEnvs :: [ModuleName] -> HomePackageTable -> HomePackageTable
retainInTopLevelEnvs keep_these hpt
   = listToHpt   [ (mod, expectJust "retain" mb_mod_info)
                 | mod <- keep_these
                 , let mb_mod_info = lookupHpt hpt mod
                 , isJust mb_mod_info ]

-- ---------------------------------------------------------------------------
-- Typecheck module loops
{-
See bug #930.  This code fixes a long-standing bug in --make.  The
problem is that when compiling the modules *inside* a loop, a data
type that is only defined at the top of the loop looks opaque; but
after the loop is done, the structure of the data type becomes
apparent.

The difficulty is then that two different bits of code have
different notions of what the data type looks like.

The idea is that after we compile a module which also has an .hs-boot
file, we re-generate the ModDetails for each of the modules that
depends on the .hs-boot file, so that everyone points to the proper
TyCons, Ids etc. defined by the real module, not the boot module.
Fortunately re-generating a ModDetails from a ModIface is easy: the
function TcIface.typecheckIface does exactly that.

Picking the modules to re-typecheck is slightly tricky.  Starting from
the module graph consisting of the modules that have already been
compiled, we reverse the edges (so they point from the imported module
to the importing module), and depth-first-search from the .hs-boot
node.  This gives us all the modules that depend transitively on the
.hs-boot module, and those are exactly the modules that we need to
re-typecheck.

Following this fix, GHC can compile itself with --make -O2.
-}

getModLoop
  :: ModSummary
  -> [ModSummary]
  -> (Module -> Bool) -- check if a module appears as a boot module in 'graph'
  -> Maybe (Set BuildModule)
getModLoop ms graph appearsAsBoot
  | not (isBootSummary ms)
  , appearsAsBoot this_mod
  , let bms = Set.fromList
          [mkBuildModule ms'
          | ms' <- reachableBackwards (ms_mod_name ms) graph
          ]
  = Just bms
  | otherwise
  = Nothing
  where this_mod = ms_mod ms

typecheckLoop :: DynFlags -> HscEnv -> [ModuleName] -> IO ()
typecheckLoop dflags hsc_env mods = do
  -- debugTraceMsg dflags 2 $
  -- pprTrace "typecheckLoop" ( text "Re-typechecking loop: " <> ppr mods) $ do
  _ <- fixIO $ \new_hpt -> do
      old_hpt <- atomicModifyIORef (hsc_HPT hsc_env) (new_hpt,)
      let hmis    = map (expectJust "typecheckLoop" . lookupHpt old_hpt) mods
      mds <- initIfaceCheck (text "typecheckLoop") hsc_env $
                mapM (handleSourceError (\e -> (liftIO . printBagOfErrors dflags . srcErrorMessages $ e) *> pure Nothing) . fmap Just . typecheckIface . hm_iface) hmis
      let new_hpt = addListToHpt old_hpt
                        (zip mods [ hmi{ hm_details = details }
                                  | (hmi, Just details) <- zip hmis mds ])
      return new_hpt
  return ()

reachableBackwards :: ModuleName -> [ModSummary] -> [ModSummary]
reachableBackwards mod summaries
  = [ node_payload node | node <- reachableG (transposeG graph) root ]
  where -- the rest just sets up the graph:
        (graph, lookup_node) = moduleGraphNodes False summaries
        root  = expectJust "reachableBackwards" (lookup_node HsBootFile mod)

-- ---------------------------------------------------------------------------
--
-- | Topological sort of the module graph
topSortModuleGraph
          :: Bool
          -- ^ Drop hi-boot nodes? (see below)
          -> ModuleGraph
          -> Maybe ModuleName
             -- ^ Root module name.  If @Nothing@, use the full graph.
          -> [SCC ModSummary]
-- ^ Calculate SCCs of the module graph, possibly dropping the hi-boot nodes
-- The resulting list of strongly-connected-components is in topologically
-- sorted order, starting with the module(s) at the bottom of the
-- dependency graph (ie compile them first) and ending with the ones at
-- the top.
--
-- Drop hi-boot nodes (first boolean arg)?
--
-- - @False@:   treat the hi-boot summaries as nodes of the graph,
--              so the graph must be acyclic
--
-- - @True@:    eliminate the hi-boot nodes, and instead pretend
--              the a source-import of Foo is an import of Foo
--              The resulting graph has no hi-boot nodes, but can be cyclic

topSortModuleGraph drop_hs_boot_nodes module_graph mb_root_mod
  = map (fmap summaryNodeSummary) $ stronglyConnCompG initial_graph
  where
    summaries = mgModSummaries module_graph
    -- stronglyConnCompG flips the original order, so if we reverse
    -- the summaries we get a stable topological sort.
    (graph, lookup_node) =
      moduleGraphNodes drop_hs_boot_nodes (reverse summaries)

    initial_graph = case mb_root_mod of
        Nothing -> graph
        Just root_mod ->
            -- restrict the graph to just those modules reachable from
            -- the specified module.  We do this by building a graph with
            -- the full set of nodes, and determining the reachable set from
            -- the specified node.
            let root | Just node <- lookup_node HsSrcFile root_mod
                     , graph `hasVertexG` node
                     = node
                     | otherwise
                     = throwGhcException (ProgramError "module does not exist")
            in graphFromEdgedVerticesUniq (seq root (reachableG graph root))

type SummaryNode = Node Int ModSummary

summaryNodeKey :: SummaryNode -> Int
summaryNodeKey = node_key

summaryNodeSummary :: SummaryNode -> ModSummary
summaryNodeSummary = node_payload

moduleGraphNodes :: Bool -> [ModSummary]
  -> (Graph SummaryNode, HscSource -> ModuleName -> Maybe SummaryNode)
moduleGraphNodes drop_hs_boot_nodes summaries =
  (graphFromEdgedVerticesUniq nodes, lookup_node)
  where
    numbered_summaries = zip summaries [1..]

    lookup_node :: HscSource -> ModuleName -> Maybe SummaryNode
    lookup_node hs_src mod = Map.lookup (mod, hscSourceToIsBoot hs_src) node_map

    lookup_key :: HscSource -> ModuleName -> Maybe Int
    lookup_key hs_src mod = fmap summaryNodeKey (lookup_node hs_src mod)

    node_map :: NodeMap SummaryNode
    node_map = Map.fromList [ ((moduleName (ms_mod s),
                                hscSourceToIsBoot (ms_hsc_src s)), node)
                            | node <- nodes
                            , let s = summaryNodeSummary node ]

    -- We use integers as the keys for the SCC algorithm
    nodes :: [SummaryNode]
    nodes = [ DigraphNode s key out_keys
            | (s, key) <- numbered_summaries
             -- Drop the hi-boot ones if told to do so
            , not (isBootSummary s && drop_hs_boot_nodes)
            , let out_keys = out_edge_keys hs_boot_key (map unLoc (ms_home_srcimps s)) ++
                             out_edge_keys HsSrcFile   (map unLoc (ms_home_imps s)) ++
                             (-- see [boot-edges] below
                              if drop_hs_boot_nodes || ms_hsc_src s == HsBootFile
                              then []
                              else case lookup_key HsBootFile (ms_mod_name s) of
                                    Nothing -> []
                                    Just k  -> [k]) ]

    -- [boot-edges] if this is a .hs and there is an equivalent
    -- .hs-boot, add a link from the former to the latter.  This
    -- has the effect of detecting bogus cases where the .hs-boot
    -- depends on the .hs, by introducing a cycle.  Additionally,
    -- it ensures that we will always process the .hs-boot before
    -- the .hs, and so the HomePackageTable will always have the
    -- most up to date information.

    -- Drop hs-boot nodes by using HsSrcFile as the key
    hs_boot_key | drop_hs_boot_nodes = HsSrcFile
                | otherwise          = HsBootFile

    out_edge_keys :: HscSource -> [ModuleName] -> [Int]
    out_edge_keys hi_boot ms = mapMaybe (lookup_key hi_boot) ms
        -- If we want keep_hi_boot_nodes, then we do lookup_key with
        -- IsBoot; else NotBoot

-- The nodes of the graph are keyed by (mod, is boot?) pairs
-- NB: hsig files show up as *normal* nodes (not boot!), since they don't
-- participate in cycles (for now)
type NodeKey   = (ModuleName, IsBoot)
type NodeMap a = Map.Map NodeKey a

msKey :: ModSummary -> NodeKey
msKey (ModSummary { ms_mod = mod, ms_hsc_src = boot })
    = (moduleName mod, hscSourceToIsBoot boot)

mkNodeMap :: [ModSummary] -> NodeMap ModSummary
mkNodeMap summaries = Map.fromList [ (msKey s, s) | s <- summaries]

nodeMapElts :: NodeMap a -> [a]
nodeMapElts = Map.elems

-- | If there are {-# SOURCE #-} imports between strongly connected
-- components in the topological sort, then those imports can
-- definitely be replaced by ordinary non-SOURCE imports: if SOURCE
-- were necessary, then the edge would be part of a cycle.
warnUnnecessarySourceImports :: GhcMonad m => [SCC ModSummary] -> m ()
warnUnnecessarySourceImports sccs = do
  dflags <- getDynFlags
  when (wopt Opt_WarnUnusedImports dflags)
    (logWarnings (listToBag (concatMap (check dflags . flattenSCC) sccs)))
  where check dflags ms =
           let mods_in_this_cycle = map ms_mod_name ms in
           [ warn dflags i | m <- ms, i <- ms_home_srcimps m,
                             unLoc i `notElem`  mods_in_this_cycle ]

        warn :: DynFlags -> Located ModuleName -> WarnMsg
        warn dflags (L loc mod) =
           mkPlainErrMsg dflags loc
                (text "Warning: {-# SOURCE #-} unnecessary in import of "
                 <+> quotes (ppr mod))


reportImportErrors :: MonadIO m => [Either ErrMsg b] -> m [b]
reportImportErrors xs | null errs = return oks
                      | otherwise = throwManyErrors errs
  where (errs, oks) = partitionEithers xs

throwManyErrors :: MonadIO m => [ErrMsg] -> m ab
throwManyErrors errs = liftIO $ throwIO $ mkSrcErr $ listToBag errs


-----------------------------------------------------------------------------
--
-- | Downsweep (dependency analysis)
--
-- Chase downwards from the specified root set, returning summaries
-- for all home modules encountered.  Only follow source-import
-- links.
--
-- We pass in the previous collection of summaries, which is used as a
-- cache to avoid recalculating a module summary if the source is
-- unchanged.
--
-- The returned list of [ModSummary] nodes has one node for each home-package
-- module, plus one for any hs-boot files.  The imports of these nodes
-- are all there, including the imports of non-home-package modules.
downsweep :: HscEnv
          -> [ModSummary]       -- Old summaries
          -> [ModuleName]       -- Ignore dependencies on these; treat
                                -- them as if they were package modules
          -> Bool               -- True <=> allow multiple targets to have
                                --          the same module name; this is
                                --          very useful for ghc -M
          -> IO [Either ErrMsg ModSummary]
                -- The elts of [ModSummary] all have distinct
                -- (Modules, IsBoot) identifiers, unless the Bool is true
                -- in which case there can be repeats
downsweep hsc_env old_summaries excl_mods allow_dup_roots
   = do
       rootSummaries <- mapM getRootSummary roots
       rootSummariesOk <- reportImportErrors rootSummaries
       let root_map = mkRootMap rootSummariesOk
       checkDuplicates root_map
       map0 <- loop (concatMap calcDeps rootSummariesOk) root_map
       -- if we have been passed -fno-code, we enable code generation
       -- for dependencies of modules that have -XTemplateHaskell,
       -- otherwise those modules will fail to compile.
       -- See Note [-fno-code mode] #8025
       map1 <- if hscTarget dflags == HscNothing
         then enableCodeGenForTH
           (defaultObjectTarget (targetPlatform dflags))
           map0
         else return map0
       return $ concat $ nodeMapElts map1
     where
        calcDeps = msDeps

        dflags = hsc_dflags hsc_env
        roots = hsc_targets hsc_env

        old_summary_map :: NodeMap ModSummary
        old_summary_map = mkNodeMap old_summaries

        getRootSummary :: Target -> IO (Either ErrMsg ModSummary)
        getRootSummary (Target (TargetFile file mb_phase) obj_allowed maybe_buf)
           = do exists <- liftIO $ doesFileExist file
                if exists
                    then Right `fmap` summariseFile hsc_env old_summaries file mb_phase
                                       obj_allowed maybe_buf
                    else return $ Left $ mkPlainErrMsg dflags noSrcSpan $
                           text "can't find file:" <+> text file
        getRootSummary (Target (TargetModule modl) obj_allowed maybe_buf)
           = do maybe_summary <- summariseModule hsc_env old_summary_map NotBoot
                                           (L rootLoc modl) obj_allowed
                                           maybe_buf excl_mods
                case maybe_summary of
                   Nothing -> return $ Left $ moduleNotFoundErr dflags modl
                   Just s  -> return s

        rootLoc = mkGeneralSrcSpan (fsLit "<command line>")

        -- In a root module, the filename is allowed to diverge from the module
        -- name, so we have to check that there aren't multiple root files
        -- defining the same module (otherwise the duplicates will be silently
        -- ignored, leading to confusing behaviour).
        checkDuplicates :: NodeMap [Either ErrMsg ModSummary] -> IO ()
        checkDuplicates root_map
           | allow_dup_roots = return ()
           | null dup_roots  = return ()
           | otherwise       = liftIO $ multiRootsErr dflags (head dup_roots)
           where
             dup_roots :: [[ModSummary]]        -- Each at least of length 2
             dup_roots = filterOut isSingleton $ map rights $ nodeMapElts root_map

        loop :: [(Located ModuleName,IsBoot)]
                        -- Work list: process these modules
             -> NodeMap [Either ErrMsg ModSummary]
                        -- Visited set; the range is a list because
                        -- the roots can have the same module names
                        -- if allow_dup_roots is True
             -> IO (NodeMap [Either ErrMsg ModSummary])
                        -- The result is the completed NodeMap
        loop [] done = return done
        loop ((wanted_mod, is_boot) : ss) done
          | Just summs <- Map.lookup key done
          = if isSingleton summs then
                loop ss done
            else
                do { multiRootsErr dflags (rights summs); return Map.empty }
          | otherwise
          = do mb_s <- summariseModule hsc_env old_summary_map
                                       is_boot wanted_mod True
                                       Nothing excl_mods
               case mb_s of
                   Nothing -> loop ss done
                   Just (Left e) -> loop ss (Map.insert key [Left e] done)
                   Just (Right s)-> do
                     new_map <-
                       loop (calcDeps s) (Map.insert key [Right s] done)
                     loop ss new_map
          where
            key = (unLoc wanted_mod, is_boot)

-- | Update the every ModSummary that is depended on
-- by a module that needs template haskell. We enable codegen to
-- the specified target, disable optimization and change the .hi
-- and .o file locations to be temporary files.
-- See Note [-fno-code mode]
enableCodeGenForTH :: HscTarget
  -> NodeMap [Either ErrMsg ModSummary]
  -> IO (NodeMap [Either ErrMsg ModSummary])
enableCodeGenForTH target nodemap =
  traverse (traverse (traverse enable_code_gen)) nodemap
  where
    enable_code_gen ms
      | ModSummary
        { ms_mod = ms_mod
        , ms_location = ms_location
        , ms_hsc_src = HsSrcFile
        , ms_hspp_opts = dflags@DynFlags
          {hscTarget = HscNothing}
        } <- ms
      , ms_mod `Set.member` needs_codegen_set
      = do
        let new_temp_file suf dynsuf = do
              tn <- newTempName dflags TFL_CurrentModule suf
              let dyn_tn = tn -<.> dynsuf
              addFilesToClean dflags TFL_GhcSession [dyn_tn]
              return tn
          -- We don't want to create .o or .hi files unless we have been asked
          -- to by the user. But we need them, so we patch their locations in
          -- the ModSummary with temporary files.
          --
        hi_file <-
          if gopt Opt_WriteInterface dflags
            then return $ ml_hi_file ms_location
            else new_temp_file (hiSuf dflags) (dynHiSuf dflags)
        o_temp_file <- new_temp_file (objectSuf dflags) (dynObjectSuf dflags)
        return $
          ms
          { ms_location =
              ms_location {ml_hi_file = hi_file, ml_obj_file = o_temp_file}
          , ms_hspp_opts = updOptLevel 0 $ dflags {hscTarget = target}
          }
      | otherwise = return ms

    needs_codegen_set = transitive_deps_set
      [ ms
      | mss <- Map.elems nodemap
      , Right ms <- mss
      , isTemplateHaskellOrQQNonBoot ms
      ]

    -- find the set of all transitive dependencies of a list of modules.
    transitive_deps_set modSums = foldl' go Set.empty modSums
      where
        go marked_mods ms@ModSummary{ms_mod}
          | ms_mod `Set.member` marked_mods = marked_mods
          | otherwise =
            let deps =
                  [ dep_ms
                  -- If a module imports a boot module, msDeps helpfully adds a
                  -- dependency to that non-boot module in it's result. This
                  -- means we don't have to think about boot modules here.
                  | (L _ mn, NotBoot) <- msDeps ms
                  , dep_ms <-
                      toList (Map.lookup (mn, NotBoot) nodemap) >>= toList >>=
                      toList
                  ]
                new_marked_mods = Set.insert ms_mod marked_mods
            in foldl' go new_marked_mods deps

mkRootMap :: [ModSummary] -> NodeMap [Either ErrMsg ModSummary]
mkRootMap summaries = Map.insertListWith (flip (++))
                                         [ (msKey s, [Right s]) | s <- summaries ]
                                         Map.empty

-- | Returns the dependencies of the ModSummary s.
-- A wrinkle is that for a {-# SOURCE #-} import we return
--      *both* the hs-boot file
--      *and* the source file
-- as "dependencies".  That ensures that the list of all relevant
-- modules always contains B.hs if it contains B.hs-boot.
-- Remember, this pass isn't doing the topological sort.  It's
-- just gathering the list of all relevant ModSummaries
msDeps :: ModSummary -> [(Located ModuleName, IsBoot)]
msDeps s =
    concat [ [(m,IsBoot), (m,NotBoot)] | m <- ms_home_srcimps s ]
        ++ [ (m,NotBoot) | m <- ms_home_imps s ]

home_imps :: [(Maybe FastString, Located ModuleName)] -> [Located ModuleName]
home_imps imps = [ lmodname |  (mb_pkg, lmodname) <- imps,
                                  isLocal mb_pkg ]
  where isLocal Nothing = True
        isLocal (Just pkg) | pkg == fsLit "this" = True -- "this" is special
        isLocal _ = False

ms_home_allimps :: ModSummary -> [ModuleName]
ms_home_allimps ms = map unLoc (ms_home_srcimps ms ++ ms_home_imps ms)

-- | Like 'ms_home_imps', but for SOURCE imports.
ms_home_srcimps :: ModSummary -> [Located ModuleName]
ms_home_srcimps = home_imps . ms_srcimps

-- | All of the (possibly) home module imports from a
-- 'ModSummary'; that is to say, each of these module names
-- could be a home import if an appropriately named file
-- existed.  (This is in contrast to package qualified
-- imports, which are guaranteed not to be home imports.)
ms_home_imps :: ModSummary -> [Located ModuleName]
ms_home_imps = home_imps . ms_imps

-----------------------------------------------------------------------------
-- Summarising modules

-- We have two types of summarisation:
--
--    * Summarise a file.  This is used for the root module(s) passed to
--      cmLoadModules.  The file is read, and used to determine the root
--      module name.  The module name may differ from the filename.
--
--    * Summarise a module.  We are given a module name, and must provide
--      a summary.  The finder is used to locate the file in which the module
--      resides.

summariseFile
        :: HscEnv
        -> [ModSummary]                 -- old summaries
        -> FilePath                     -- source file name
        -> Maybe Phase                  -- start phase
        -> Bool                         -- object code allowed?
        -> Maybe (StringBuffer,UTCTime)
        -> IO ModSummary

summariseFile hsc_env old_summaries file mb_phase obj_allowed maybe_buf
        -- we can use a cached summary if one is available and the
        -- source file hasn't changed,  But we have to look up the summary
        -- by source file, rather than module name as we do in summarise.
   | Just old_summary <- findSummaryBySourceFile old_summaries file
   = do
        let location = ms_location old_summary
            dflags = hsc_dflags hsc_env

        src_timestamp <- get_src_timestamp
                -- The file exists; we checked in getRootSummary above.
                -- If it gets removed subsequently, then this
                -- getModificationUTCTime may fail, but that's the right
                -- behaviour.

                -- return the cached summary if the source didn't change
        if ms_hs_date old_summary == src_timestamp &&
           not (gopt Opt_ForceRecomp (hsc_dflags hsc_env))
           then do -- update the object-file timestamp
                  obj_timestamp <-
                    if isObjectTarget (hscTarget (hsc_dflags hsc_env))
                        || obj_allowed -- bug #1205
                        then liftIO $ getObjTimestamp location NotBoot
                        else return Nothing
                  hi_timestamp <- maybeGetIfaceDate dflags location

                  -- We have to repopulate the Finder's cache because it
                  -- was flushed before the downsweep.
                  _ <- liftIO $ addHomeModuleToFinder hsc_env
                    (moduleName (ms_mod old_summary)) (ms_location old_summary)

                  return old_summary{ ms_obj_date = obj_timestamp
                                    , ms_iface_date = hi_timestamp }
           else
                new_summary src_timestamp

   | otherwise
   = do src_timestamp <- get_src_timestamp
        new_summary src_timestamp
  where
    get_src_timestamp = case maybe_buf of
                           Just (_,t) -> return t
                           Nothing    -> liftIO $ getModificationUTCTime file
                        -- getModificationUTCTime may fail

    new_summary src_timestamp = do
        let dflags = hsc_dflags hsc_env

        let hsc_src = if isHaskellSigFilename file then HsigFile else HsSrcFile

        (dflags', hspp_fn, buf)
            <- preprocessFile hsc_env file mb_phase maybe_buf

        (srcimps,the_imps, L _ mod_name) <- getImports dflags' buf hspp_fn file

        -- Make a ModLocation for this file
        location <- liftIO $ mkHomeModLocation dflags mod_name file

        -- Tell the Finder cache where it is, so that subsequent calls
        -- to findModule will find it, even if it's not on any search path
        mod <- liftIO $ addHomeModuleToFinder hsc_env mod_name location

        -- when the user asks to load a source file by name, we only
        -- use an object file if -fobject-code is on.  See #1205.
        obj_timestamp <-
            if isObjectTarget (hscTarget (hsc_dflags hsc_env))
               || obj_allowed -- bug #1205
                then liftIO $ modificationTimeIfExists (ml_obj_file location)
                else return Nothing

        hi_timestamp <- maybeGetIfaceDate dflags location

        extra_sig_imports <- findExtraSigImports hsc_env hsc_src mod_name
        required_by_imports <- implicitRequirements hsc_env the_imps

        return (ModSummary { ms_mod = mod,
                             ms_hsc_src = hsc_src,
                             ms_location = location,
                             ms_hspp_file = hspp_fn,
                             ms_hspp_opts = dflags',
                             ms_hspp_buf  = Just buf,
                             ms_parsed_mod = Nothing,
                             ms_srcimps = srcimps,
                             ms_textual_imps = the_imps ++ extra_sig_imports ++ required_by_imports,
                             ms_hs_date = src_timestamp,
                             ms_iface_date = hi_timestamp,
                             ms_obj_date = obj_timestamp })

findSummaryBySourceFile :: [ModSummary] -> FilePath -> Maybe ModSummary
findSummaryBySourceFile summaries file
  = case [ ms | ms <- summaries, HsSrcFile <- [ms_hsc_src ms],
                                 expectJust "findSummaryBySourceFile" (ml_hs_file (ms_location ms)) == file ] of
        [] -> Nothing
        (x:_) -> Just x

-- Summarise a module, and pick up source and timestamp.
summariseModule
          :: HscEnv
          -> NodeMap ModSummary -- Map of old summaries
          -> IsBoot             -- IsBoot <=> a {-# SOURCE #-} import
          -> Located ModuleName -- Imported module to be summarised
          -> Bool               -- object code allowed?
          -> Maybe (StringBuffer, UTCTime)
          -> [ModuleName]               -- Modules to exclude
          -> IO (Maybe (Either ErrMsg ModSummary))      -- Its new summary

summariseModule hsc_env old_summary_map is_boot (L loc wanted_mod)
                obj_allowed maybe_buf excl_mods
  | wanted_mod `elem` excl_mods
  = return Nothing

  | Just old_summary <- Map.lookup (wanted_mod, is_boot) old_summary_map
  = do          -- Find its new timestamp; all the
                -- ModSummaries in the old map have valid ml_hs_files
        let location = ms_location old_summary
            src_fn = expectJust "summariseModule" (ml_hs_file location)

                -- check the modification time on the source file, and
                -- return the cached summary if it hasn't changed.  If the
                -- file has disappeared, we need to call the Finder again.
        case maybe_buf of
           Just (_,t) -> check_timestamp old_summary location src_fn t
           Nothing    -> do
                m <- tryIO (getModificationUTCTime src_fn)
                case m of
                   Right t -> check_timestamp old_summary location src_fn t
                   Left e | isDoesNotExistError e -> find_it
                          | otherwise             -> ioError e

  | otherwise  = find_it
  where
    dflags = hsc_dflags hsc_env

    check_timestamp old_summary location src_fn src_timestamp
        | ms_hs_date old_summary == src_timestamp &&
          not (gopt Opt_ForceRecomp dflags) = do
                -- update the object-file timestamp
                obj_timestamp <-
                    if isObjectTarget (hscTarget (hsc_dflags hsc_env))
                       || obj_allowed -- bug #1205
                       then getObjTimestamp location is_boot
                       else return Nothing
                hi_timestamp <- maybeGetIfaceDate dflags location
                return (Just (Right old_summary{ ms_obj_date = obj_timestamp
                                               , ms_iface_date = hi_timestamp}))
        | otherwise =
                -- source changed: re-summarise.
                new_summary location (ms_mod old_summary) src_fn src_timestamp

    find_it = do
        found <- findImportedModule hsc_env wanted_mod Nothing
        case found of
             Found location mod
                | isJust (ml_hs_file location) ->
                        -- Home package
                         just_found location mod

             _ -> return Nothing
                        -- Not found
                        -- (If it is TRULY not found at all, we'll
                        -- error when we actually try to compile)

    just_found location mod = do
                -- Adjust location to point to the hs-boot source file,
                -- hi file, object file, when is_boot says so
        let location' | IsBoot <- is_boot = addBootSuffixLocn location
                      | otherwise         = location
            src_fn = expectJust "summarise2" (ml_hs_file location')

                -- Check that it exists
                -- It might have been deleted since the Finder last found it
        maybe_t <- modificationTimeIfExists src_fn
        case maybe_t of
          Nothing -> return $ Just $ Left $ noHsFileErr dflags loc src_fn
          Just t  -> new_summary location' mod src_fn t


    new_summary location mod src_fn src_timestamp
      = do
        -- Preprocess the source file and get its imports
        -- The dflags' contains the OPTIONS pragmas
        (dflags', hspp_fn, buf) <- preprocessFile hsc_env src_fn Nothing maybe_buf
        (srcimps, the_imps, L mod_loc mod_name) <- getImports dflags' buf hspp_fn src_fn

        -- NB: Despite the fact that is_boot is a top-level parameter, we
        -- don't actually know coming into this function what the HscSource
        -- of the module in question is.  This is because we may be processing
        -- this module because another module in the graph imported it: in this
        -- case, we know if it's a boot or not because of the {-# SOURCE #-}
        -- annotation, but we don't know if it's a signature or a regular
        -- module until we actually look it up on the filesystem.
        let hsc_src = case is_boot of
                IsBoot -> HsBootFile
                _ | isHaskellSigFilename src_fn -> HsigFile
                  | otherwise -> HsSrcFile

        when (mod_name /= wanted_mod) $
                throwOneError $ mkPlainErrMsg dflags' mod_loc $
                              text "File name does not match module name:"
                              $$ text "Saw:" <+> quotes (ppr mod_name)
                              $$ text "Expected:" <+> quotes (ppr wanted_mod)

        when (hsc_src == HsigFile && isNothing (lookup mod_name (thisUnitIdInsts dflags))) $
            let suggested_instantiated_with =
                    hcat (punctuate comma $
                        [ ppr k <> text "=" <> ppr v
                        | (k,v) <- ((mod_name, mkHoleModule mod_name)
                                : thisUnitIdInsts dflags)
                        ])
            in throwOneError $ mkPlainErrMsg dflags' mod_loc $
                text "Unexpected signature:" <+> quotes (ppr mod_name)
                $$ if gopt Opt_BuildingCabalPackage dflags
                    then parens (text "Try adding" <+> quotes (ppr mod_name)
                            <+> text "to the"
                            <+> quotes (text "signatures")
                            <+> text "field in your Cabal file.")
                    else parens (text "Try passing -instantiated-with=\"" <>
                                 suggested_instantiated_with <> text "\"" $$
                                text "replacing <" <> ppr mod_name <> text "> as necessary.")

                -- Find the object timestamp, and return the summary
        obj_timestamp <-
           if isObjectTarget (hscTarget (hsc_dflags hsc_env))
              || obj_allowed -- bug #1205
              then getObjTimestamp location is_boot
              else return Nothing

        hi_timestamp <- maybeGetIfaceDate dflags location

        extra_sig_imports <- findExtraSigImports hsc_env hsc_src mod_name
        required_by_imports <- implicitRequirements hsc_env the_imps

        return (Just (Right (ModSummary { ms_mod       = mod,
                              ms_hsc_src   = hsc_src,
                              ms_location  = location,
                              ms_hspp_file = hspp_fn,
                              ms_hspp_opts = dflags',
                              ms_hspp_buf  = Just buf,
                              ms_parsed_mod = Nothing,
                              ms_srcimps      = srcimps,
                              ms_textual_imps = the_imps ++ extra_sig_imports ++ required_by_imports,
                              ms_hs_date   = src_timestamp,
                              ms_iface_date = hi_timestamp,
                              ms_obj_date  = obj_timestamp })))


getObjTimestamp :: ModLocation -> IsBoot -> IO (Maybe UTCTime)
getObjTimestamp location is_boot
  = if is_boot == IsBoot then return Nothing
                         else modificationTimeIfExists (ml_obj_file location)


preprocessFile :: HscEnv
               -> FilePath
               -> Maybe Phase -- ^ Starting phase
               -> Maybe (StringBuffer,UTCTime)
               -> IO (DynFlags, FilePath, StringBuffer)
preprocessFile hsc_env src_fn mb_phase Nothing
  = do
        (dflags', hspp_fn) <- preprocess hsc_env (src_fn, mb_phase)
        buf <- hGetStringBuffer hspp_fn
        return (dflags', hspp_fn, buf)

preprocessFile hsc_env src_fn mb_phase (Just (buf, _time))
  = do
        let dflags = hsc_dflags hsc_env
        let local_opts = getOptions dflags buf src_fn

        (dflags', leftovers, warns)
            <- parseDynamicFilePragma dflags local_opts
        checkProcessArgsResult dflags leftovers
        handleFlagWarnings dflags' warns

        let needs_preprocessing
                | Just (Unlit _) <- mb_phase    = True
                | Nothing <- mb_phase, Unlit _ <- startPhase src_fn  = True
                  -- note: local_opts is only required if there's no Unlit phase
                | xopt LangExt.Cpp dflags'      = True
                | gopt Opt_Pp  dflags'          = True
                | otherwise                     = False

        when needs_preprocessing $
           throwGhcExceptionIO (ProgramError "buffer needs preprocesing; interactive check disabled")

        return (dflags', src_fn, buf)


-----------------------------------------------------------------------------
--                      Error messages
-----------------------------------------------------------------------------

noModError :: DynFlags -> SrcSpan -> ModuleName -> FindResult -> ErrMsg
-- ToDo: we don't have a proper line number for this error
noModError dflags loc wanted_mod err
  = mkPlainErrMsg dflags loc $ cannotFindModule dflags wanted_mod err

noHsFileErr :: DynFlags -> SrcSpan -> String -> ErrMsg
noHsFileErr dflags loc path
  = mkPlainErrMsg dflags loc $ text "Can't find" <+> text path

moduleNotFoundErr :: DynFlags -> ModuleName -> ErrMsg
moduleNotFoundErr dflags mod
  = mkPlainErrMsg dflags noSrcSpan $
        text "module" <+> quotes (ppr mod) <+> text "cannot be found locally"

multiRootsErr :: DynFlags -> [ModSummary] -> IO ()
multiRootsErr _      [] = panic "multiRootsErr"
multiRootsErr dflags summs@(summ1:_)
  = throwOneError $ mkPlainErrMsg dflags noSrcSpan $
        text "module" <+> quotes (ppr mod) <+>
        text "is defined in multiple files:" <+>
        sep (map text files)
  where
    mod = ms_mod summ1
    files = map (expectJust "checkDup" . ml_hs_file . ms_location) summs

cyclicModuleErr :: [ModSummary] -> SDoc
-- From a strongly connected component we find
-- a single cycle to report
cyclicModuleErr mss
  = ASSERT( not (null mss) )
    case findCycle graph of
       Nothing   -> text "Unexpected non-cycle" <+> ppr mss
       Just path -> vcat [ text "Module imports form a cycle:"
                         , nest 2 (show_path path) ]
  where
    graph :: [Node NodeKey ModSummary]
    graph = [ DigraphNode ms (msKey ms) (get_deps ms) | ms <- mss]

    get_deps :: ModSummary -> [NodeKey]
    get_deps ms = ([ (unLoc m, IsBoot)  | m <- ms_home_srcimps ms ] ++
                   [ (unLoc m, NotBoot) | m <- ms_home_imps    ms ])

    show_path []         = panic "show_path"
    show_path [m]        = text "module" <+> ppr_ms m
                           <+> text "imports itself"
    show_path (m1:m2:ms) = vcat ( nest 7 (text "module" <+> ppr_ms m1)
                                : nest 6 (text "imports" <+> ppr_ms m2)
                                : go ms )
       where
         go []     = [text "which imports" <+> ppr_ms m1]
         go (m:ms) = (text "which imports" <+> ppr_ms m) : go ms


    ppr_ms :: ModSummary -> SDoc
    ppr_ms ms = quotes (ppr (moduleName (ms_mod ms))) <+>
                (parens (text (msHsFilePath ms)))
