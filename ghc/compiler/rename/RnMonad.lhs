%
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[RnMonad]{The monad used by the renamer}

\begin{code}
module RnMonad(
	module RnMonad,

	module RdrName,		-- Re-exports
	module Name,		-- from these two

	Module,
	FiniteMap,
	Bag,
	RdrNameHsDecl,
	RdrNameInstDecl,
	Version,
	NameSet,
	OccName,
	Fixity
    ) where

#include "HsVersions.h"

import HsSyn		
import RdrHsSyn
import RnHsSyn		( RenamedFixitySig )
import HscTypes		( AvailEnv, emptyAvailEnv, lookupType,
			  NameSupply(..), 
			  ImportedModuleInfo, WhetherHasOrphans, ImportVersion, 
			  PersistentRenamerState(..),  RdrExportItem,
			  DeclsMap, IfaceInsts, IfaceRules, 
			  HomeSymbolTable, TyThing,
			  PersistentCompilerState(..), GlobalRdrEnv, 
			  LocalRdrEnv,
			  HomeIfaceTable, PackageIfaceTable )
import BasicTypes	( Version, defaultFixity, 
			  Fixity(..), FixityDirection(..) )
import ErrUtils		( addShortErrLocLine, addShortWarnLocLine,
			  Message, Messages, errorsFound, warningsFound,
			  printErrorsAndWarnings
			)
import RdrName		( RdrName, dummyRdrVarName, rdrNameModule, rdrNameOcc,
			  RdrNameEnv, emptyRdrEnv, extendRdrEnv, 
			  addListToRdrEnv, rdrEnvToList, rdrEnvElts
			)
import Id		( idName )
import MkId		( seqId )
import Name		( Name, OccName, NamedThing(..), 
			  nameOccName, nameRdrName,
			  decode, mkInternalName
			)
import NameEnv		( NameEnv, lookupNameEnv, emptyNameEnv,
			  extendNameEnvList )
import Module		( Module, ModuleName, ModuleSet, emptyModuleSet,
			  PackageName, preludePackage )
import PrelInfo		( ghcPrimExports, 
			  cCallableClassDecl, cReturnableClassDecl, assertDecl )
import PrelNames	( mkUnboundName, gHC_PRIM_Name )
import NameSet		
import CmdLineOpts	( DynFlags, DynFlag(..), dopt )
import SrcLoc		( SrcLoc, generatedSrcLoc, noSrcLoc )
import Unique		( Unique )
import FiniteMap	( FiniteMap )
import Maybes		( seqMaybe )
import Bag		( Bag, emptyBag, isEmptyBag, snocBag )
import UniqSupply
import Outputable

import IOExts		( IORef, newIORef, readIORef, writeIORef, 
			  fixIO, unsafePerformIO )
import IO		( hPutStr, stderr )
	
infixr 9 `thenRn`, `thenRn_`
\end{code}


%************************************************************************
%*									*
\subsection{Somewhat magical interface to other monads}
%*									*
%************************************************************************

\begin{code}
ioToRnM :: IO r -> RnM d (Either IOError r)
ioToRnM io rn_down g_down = (io >>= \ ok -> return (Right ok)) 
			    `catch` 
			    (\ err -> return (Left err))

ioToRnM_no_fail :: IO r -> RnM d r
ioToRnM_no_fail io rn_down g_down 
   = (io >>= \ ok -> return ok) 
     `catch` 
     (\ err -> panic "ioToRnM_no_fail: the I/O operation failed!")
	    
traceRn :: SDoc -> RnM d ()
traceRn msg = ifOptRn Opt_D_dump_rn_trace (putDocRn msg)

traceHiDiffsRn :: SDoc -> RnM d ()
traceHiDiffsRn msg = ifOptRn Opt_D_dump_hi_diffs (putDocRn msg)

putDocRn :: SDoc -> RnM d ()
putDocRn msg = ioToRnM (printErrs alwaysQualify msg)	`thenRn_`
	       returnRn ()
\end{code}


%************************************************************************
%*									*
\subsection{Data types}
%*									*
%************************************************************************

%===================================================
\subsubsection{		MONAD TYPES}
%===================================================

\begin{code}
type RnM d r = RnDown -> d -> IO r
type RnMS r  = RnM SDown r		-- Renaming source
type RnMG r  = RnM ()    r		-- Getting global names etc

	-- Common part
data RnDown
  = RnDown {
	rn_mod     :: Module,		-- This module
	rn_loc     :: SrcLoc,		-- Current locn

	rn_dflags  :: DynFlags,

	rn_hit     :: HomeIfaceTable,
	rn_done    :: Name -> Maybe TyThing,	-- Tells what things (both in the
						-- home package and other packages)
						-- were already available (i.e. in
						-- the relevant SymbolTable) before 
						-- compiling this module
			-- The Name passed to rn_done is guaranteed to be a Global,
			-- so it has a Module, so it can be looked up

	rn_errs    :: IORef Messages,
	rn_ns      :: IORef NameSupply,
	rn_ifaces  :: IORef Ifaces
    }

	-- For renaming source code
data SDown = SDown {
		  rn_mode :: RnMode,

		  rn_genv :: GlobalRdrEnv,	-- Top level environment

		  rn_avails :: AvailEnv,	
			-- Top level AvailEnv; contains all the things that
			-- are nameable in the top-level scope, regardless of
			-- *how* they can be named (qualified, unqualified...)
			-- It is used only to map a Class to its class ops, and 
			-- hence to resolve the binders in an instance decl

		  rn_lenv :: LocalRdrEnv,	-- Local name envt
			--   Does *not* include global name envt; may shadow it
			--   Includes both ordinary variables and type variables;
			--   they are kept distinct because tyvar have a different
			--   occurrence contructor (Name.TvOcc)
			-- We still need the unsullied global name env so that
			--   we can look up record field names

		  rn_fixenv :: LocalFixityEnv	-- Local fixities (for non-top-level
						-- declarations)
			-- The global fixities are held in the
			-- HIT or PIT.  Why?  See the comments
			-- with RnIfaces.lookupLocalFixity
		}

data RnMode	= SourceMode		-- Renaming source code
		| InterfaceMode		-- Renaming interface declarations.  
		| CmdLineMode		-- Renaming a command-line expression

isInterfaceMode InterfaceMode = True
isInterfaceMode _ = False

isCmdLineMode CmdLineMode = True
isCmdLineMode _ = False
\end{code}

\begin{code}
type LocalFixityEnv = NameEnv RenamedFixitySig
	-- We keep the whole fixity sig so that we
	-- can report line-number info when there is a duplicate
	-- fixity declaration

emptyLocalFixityEnv :: LocalFixityEnv
emptyLocalFixityEnv = emptyNameEnv
\end{code}


%************************************************************************
%*									*
\subsection{Interface file stuff}
%*									*
%************************************************************************

\begin{code}
type IfaceDeprecs = Maybe (Either DeprecTxt [(RdrName,DeprecTxt)])
	-- Nothing	  => NoDeprecs
	-- Just (Left t)  => DeprecAll
	-- Just (Right p) => DeprecSome

data ParsedIface
  = ParsedIface {
      pi_mod	   :: ModuleName,
      pi_pkg       :: PackageName,
      pi_vers	   :: Version,		 		-- Module version number
      pi_orphan    :: WhetherHasOrphans,		-- Whether this module has orphans
      pi_usages	   :: [ImportVersion OccName],		-- Usages
      pi_exports   :: (Version, [RdrExportItem]),	-- Exports
      pi_decls	   :: [(Version, RdrNameTyClDecl)],	-- Local definitions
      pi_fixity	   :: [(RdrName,Fixity)],		-- Local fixity declarations,
      pi_insts	   :: [RdrNameInstDecl],		-- Local instance declarations
      pi_rules	   :: (Version, [RdrNameRuleDecl]),	-- Rules, with their version
      pi_deprecs   :: IfaceDeprecs			-- Deprecations
    }
\end{code}

%************************************************************************
%*									*
\subsection{Wired-in interfaces}
%*									*
%************************************************************************

\begin{code}
ghcPrimIface :: ParsedIface
ghcPrimIface = ParsedIface {
      pi_mod	 = gHC_PRIM_Name,
      pi_pkg     = preludePackage,
      pi_vers    = 1,
      pi_orphan  = False,
      pi_usages  = [],
      pi_exports = (1, [(gHC_PRIM_Name, ghcPrimExports)]),
      pi_decls   = [(1,cCallableClassDecl), 
		    (1,cReturnableClassDecl), 
		    (1,assertDecl)],
      pi_fixity  = [(nameRdrName (idName seqId), Fixity 0 InfixR)],
		-- seq is infixr 0
      pi_insts   = [],
      pi_rules   = (1,[]),
      pi_deprecs = Nothing
 }
\end{code}

%************************************************************************
%*									*
\subsection{The renamer state}
%*									*
%************************************************************************

\begin{code}
data Ifaces = Ifaces {
    -- PERSISTENT FIELDS
	iPIT :: PackageIfaceTable,
		-- The ModuleIFaces for modules in other packages
		-- whose interfaces we have opened
		-- The declarations in these interface files are held in
		-- iDecls, iInsts, iRules (below), not in the mi_decls fields
		-- of the iPIT.  What _is_ in the iPIT is:
		--	* The Module 
		--	* Version info
		--	* Its exports
		--	* Fixities
		--	* Deprecations
		-- The iPIT field is initialised from the compiler's persistent
		-- package symbol table, and the renamer incrementally adds
		-- to it.

	iImpModInfo :: ImportedModuleInfo,
			-- Modules that we know something about, because they are mentioned
			-- in interface files, BUT which we have not loaded yet.  
			-- No module is both in here and in the PIT

	iDecls :: DeclsMap,	
		-- A single, global map of Names to unslurped decls

	iInsts :: IfaceInsts,
		-- The as-yet un-slurped instance decls; this bag is depleted when we
		-- slurp an instance decl so that we don't slurp the same one twice.
		-- Each is 'gated' by the names that must be available before
		-- this instance decl is needed.

	iRules :: IfaceRules,
		-- Similar to instance decls, only for rules

    -- EPHEMERAL FIELDS
    -- These fields persist during the compilation of a single module only
	iSlurp :: NameSet,
		-- All the names (whether "big" or "small", whether wired-in or not,
		-- whether locally defined or not) that have been slurped in so far.
		--
		-- It's used for two things:
		--	a) To record what we've already slurped, so
		--	   we can no-op if we try to slurp it again
		--	b) As the 'gates' for importing rules.  We import a rule
		--	   if all its LHS free vars have been slurped

	iVSlurp :: (ModuleSet, NameSet)
		-- The Names are all the (a) non-wired-in
		--			 (b) "big"
		--	   		 (c) non-locally-defined
		--	   		 (d) home-package
		-- names that have been slurped in so far, with their versions.
		-- This is used to generate the "usage" information for this module.
		-- Subset of the previous field.
		--
		-- The module set is the non-home-package modules from which we have
		-- slurped at least one name.
		-- It's worth keeping separately, because there's no very easy 
		-- way to distinguish the "big" names from the "non-big" ones.
		-- But this is a decision we might want to revisit.
    }
\end{code}


%************************************************************************
%*									*
\subsection{Main monad code}
%*									*
%************************************************************************

\begin{code}
runRn dflags hit hst pcs mod do_rn
  = do { (pcs, msgs, r) <- initRn dflags hit hst pcs mod do_rn ;
	 printErrorsAndWarnings alwaysQualify msgs ;
	 return (pcs, errorsFound msgs, r)
    }

initRn :: DynFlags
       -> HomeIfaceTable -> HomeSymbolTable
       -> PersistentCompilerState
       -> Module
       -> RnMG t
       -> IO (PersistentCompilerState, Messages, t)	

initRn dflags hit hst pcs mod do_rn
  = do 
	let prs = pcs_PRS pcs
	let pte = pcs_PTE pcs
	let ifaces = Ifaces { iPIT   = pcs_PIT pcs,
			      iDecls = prsDecls prs,
		  	      iInsts = prsInsts prs,
		 	      iRules = prsRules prs,

		 	      iImpModInfo = prsImpMods prs,
			      iSlurp      = unitNameSet (mkUnboundName dummyRdrVarName),
				-- Pretend that the dummy unbound name has already been
				-- slurped.  This is what's returned for an out-of-scope name,
				-- and we don't want thereby to try to suck it in!
			      iVSlurp = (emptyModuleSet, emptyNameSet)
		      }
	names_var <- newIORef (prsOrig prs)
	errs_var  <- newIORef (emptyBag,emptyBag)
	iface_var <- newIORef ifaces
	let rn_down = RnDown { rn_mod = mod,
			       rn_loc = noSrcLoc, 
	
			       rn_dflags = dflags,
			       rn_hit    = hit,
			       rn_done   = lookupType hst pte,
					     
			       rn_ns     = names_var, 
			       rn_errs   = errs_var, 
			       rn_ifaces = iface_var,
			     }
	
	-- do the business
	res <- do_rn rn_down ()
	
	-- Grab state and record it
	(warns, errs) 	<- readIORef errs_var
	new_ifaces    	<- readIORef iface_var
	new_orig	<- readIORef names_var
	let new_prs = prs { prsOrig    = new_orig,
			    prsImpMods = iImpModInfo new_ifaces,
			    prsDecls   = iDecls new_ifaces,
			    prsInsts   = iInsts new_ifaces,
			    prsRules   = iRules new_ifaces }
	let new_pcs = pcs { pcs_PIT = iPIT new_ifaces, 
			    pcs_PRS = new_prs }
	
	return (new_pcs, (warns, errs), res)

initRnMS :: GlobalRdrEnv -> AvailEnv -> LocalRdrEnv -> LocalFixityEnv -> RnMode
	 -> RnMS a -> RnM d a

initRnMS rn_env avails local_env fixity_env mode thing_inside rn_down g_down
	-- The fixity_env appears in both the rn_fixenv field
	-- and in the HIT.  See comments with RnHiFiles.lookupFixityRn
  = let
	s_down = SDown { rn_genv = rn_env, rn_avails = avails, 
			 rn_lenv = local_env, rn_fixenv = fixity_env, 
			 rn_mode = mode }
    in
    thing_inside rn_down s_down

initIfaceRnMS :: Module -> RnMS r -> RnM d r
initIfaceRnMS mod thing_inside 
  = initRnMS emptyRdrEnv emptyAvailEnv emptyRdrEnv 
	     emptyLocalFixityEnv InterfaceMode
	     (setModuleRn mod thing_inside)
\end{code}

@renameDerivedCode@ is used to rename stuff ``out-of-line'';
that is, not as part of the main renamer.
Sole examples: derived definitions,
which are only generated in the type checker.

The @NameSupply@ includes a @UniqueSupply@, so if you call it more than
once you must either split it, or install a fresh unique supply.

\begin{code}
renameDerivedCode :: DynFlags 
		  -> Module
		  -> PersistentRenamerState
	          -> RnMS r
	          -> r

renameDerivedCode dflags mod prs thing_inside
  = unsafePerformIO $
	-- It's not really unsafe!  When renaming source code we
	-- only do any I/O if we need to read in a fixity declaration;
	-- and that doesn't happen in pragmas etc

    do	{ us <- mkSplitUniqSupply 'r'
	; names_var <- newIORef ((prsOrig prs) { nsUniqs = us })
	; errs_var <- newIORef (emptyBag,emptyBag)

    	; let rn_down = RnDown { rn_dflags = dflags,
			       	 rn_loc    = generatedSrcLoc, rn_ns = names_var,
			       	 rn_errs   = errs_var, 
			       	 rn_mod    = mod, 
			       	 rn_done   = bogus "rn_done",	
				 rn_hit    = bogus "rn_hit",
			       	 rn_ifaces = bogus "rn_ifaces"
			       }
	; let s_down = SDown { rn_mode = InterfaceMode, 
			       -- So that we can refer to PrelBase.True etc
			       rn_avails = emptyAvailEnv,
			       rn_genv = emptyRdrEnv, rn_lenv = emptyRdrEnv,
			       rn_fixenv = emptyLocalFixityEnv }

	; result <- thing_inside rn_down s_down
	; messages <- readIORef errs_var

	; if bad messages then
		do { hPutStr stderr "Urk!  renameDerivedCode found errors or warnings"
		   ; printErrorsAndWarnings alwaysQualify messages
		   }
	   else
		return()

	; return result
	}
  where
#ifdef DEBUG
    bad messages = errorsFound messages || warningsFound messages
#else
    bad messages = errorsFound messages
#endif

bogus s = panic ("rnameSourceCode: " ++ s)  -- Used for unused record fields

{-# INLINE thenRn #-}
{-# INLINE thenRn_ #-}
{-# INLINE returnRn #-}
{-# INLINE andRn #-}

returnRn :: a -> RnM d a
thenRn   :: RnM d a -> (a -> RnM d b) -> RnM d b
thenRn_  :: RnM d a -> RnM d b -> RnM d b
andRn    :: (a -> a -> a) -> RnM d a -> RnM d a -> RnM d a
mapRn    :: (a -> RnM d b) -> [a] -> RnM d [b]
mapRn_   :: (a -> RnM d b) -> [a] -> RnM d ()
mapMaybeRn :: (a -> RnM d (Maybe b)) -> [a] -> RnM d [b]
flatMapRn  :: (a -> RnM d [b])       -> [a] -> RnM d [b]
sequenceRn  :: [RnM d a] -> RnM d [a]
sequenceRn_ :: [RnM d a] -> RnM d ()
foldlRn :: (b  -> a -> RnM d b) -> b -> [a] -> RnM d b
mapAndUnzipRn :: (a -> RnM d (b,c)) -> [a] -> RnM d ([b],[c])
fixRn    :: (a -> RnM d a) -> RnM d a

returnRn v gdown ldown  = return v
thenRn m k gdown ldown  = m gdown ldown >>= \ r -> k r gdown ldown
thenRn_ m k gdown ldown = m gdown ldown >> k gdown ldown
fixRn m gdown ldown = fixIO (\r -> m r gdown ldown)
andRn combiner m1 m2 gdown ldown
  = m1 gdown ldown >>= \ res1 ->
    m2 gdown ldown >>= \ res2 ->
    return (combiner res1 res2)

sequenceRn []     = returnRn []
sequenceRn (m:ms) =  m			`thenRn` \ r ->
		     sequenceRn ms	`thenRn` \ rs ->
		     returnRn (r:rs)

sequenceRn_ []     = returnRn ()
sequenceRn_ (m:ms) = m `thenRn_` sequenceRn_ ms

mapRn f []     = returnRn []
mapRn f (x:xs)
  = f x		`thenRn` \ r ->
    mapRn f xs 	`thenRn` \ rs ->
    returnRn (r:rs)

mapRn_ f []     = returnRn ()
mapRn_ f (x:xs) = 
    f x		`thenRn_`
    mapRn_ f xs

foldlRn k z [] = returnRn z
foldlRn k z (x:xs) = k z x	`thenRn` \ z' ->
		     foldlRn k z' xs

mapAndUnzipRn f [] = returnRn ([],[])
mapAndUnzipRn f (x:xs)
  = f x		    	`thenRn` \ (r1,  r2)  ->
    mapAndUnzipRn f xs	`thenRn` \ (rs1, rs2) ->
    returnRn (r1:rs1, r2:rs2)

mapAndUnzip3Rn f [] = returnRn ([],[],[])
mapAndUnzip3Rn f (x:xs)
  = f x		    	`thenRn` \ (r1,  r2,  r3)  ->
    mapAndUnzip3Rn f xs	`thenRn` \ (rs1, rs2, rs3) ->
    returnRn (r1:rs1, r2:rs2, r3:rs3)

mapMaybeRn f []     = returnRn []
mapMaybeRn f (x:xs) = f x		`thenRn` \ maybe_r ->
		      mapMaybeRn f xs 	`thenRn` \ rs ->
		      case maybe_r of
			Nothing -> returnRn rs
			Just r  -> returnRn (r:rs)

flatMapRn f []     = returnRn []
flatMapRn f (x:xs) = f x 		`thenRn` \ r ->
		     flatMapRn f xs	`thenRn` \ rs ->
		     returnRn (r ++ rs)
\end{code}



%************************************************************************
%*									*
\subsection{Boring plumbing for common part}
%*									*
%************************************************************************


%================
\subsubsection{  Errors and warnings}
%=====================

\begin{code}
failWithRn :: a -> Message -> RnM d a
failWithRn res msg (RnDown {rn_errs = errs_var, rn_loc = loc}) l_down
  = readIORef  errs_var  					>>=  \ (warns,errs) ->
    writeIORef errs_var (warns, errs `snocBag` err)		>> 
    return res
  where
    err = addShortErrLocLine loc msg

warnWithRn :: a -> Message -> RnM d a
warnWithRn res msg (RnDown {rn_errs = errs_var, rn_loc = loc}) l_down
  = readIORef  errs_var  				 	>>=  \ (warns,errs) ->
    writeIORef errs_var (warns `snocBag` warn, errs)	>> 
    return res
  where
    warn = addShortWarnLocLine loc msg

tryRn :: RnM d a -> RnM d (Either Messages a)
tryRn try_this down@(RnDown {rn_errs = errs_var}) l_down
  = do current_msgs <- readIORef errs_var
       writeIORef errs_var (emptyBag,emptyBag)
       a <- try_this down l_down
       (warns, errs) <- readIORef errs_var
       writeIORef errs_var current_msgs
       if (isEmptyBag errs)
	  then return (Right a)
	  else return (Left (warns,errs))

setErrsRn :: Messages -> RnM d ()
setErrsRn msgs down@(RnDown {rn_errs = errs_var}) l_down
  = do writeIORef errs_var msgs; return ()

addErrRn :: Message -> RnM d ()
addErrRn err = failWithRn () err

checkRn :: Bool -> Message -> RnM d ()	-- Check that a condition is true
checkRn False err = addErrRn err
checkRn True  err = returnRn ()

warnCheckRn :: Bool -> Message -> RnM d ()	-- Check that a condition is true
warnCheckRn False err = addWarnRn err
warnCheckRn True  err = returnRn ()

addWarnRn :: Message -> RnM d ()
addWarnRn warn = warnWithRn () warn

checkErrsRn :: RnM d Bool		-- True <=> no errors so far
checkErrsRn (RnDown {rn_errs = errs_var}) l_down
  = readIORef  errs_var  				 	>>=  \ (warns,errs) ->
    return (isEmptyBag errs)

doptRn :: DynFlag -> RnM d Bool
doptRn dflag (RnDown { rn_dflags = dflags}) l_down
   = return (dopt dflag dflags)

ifOptRn :: DynFlag -> RnM d a -> RnM d ()
ifOptRn dflag thing_inside down@(RnDown { rn_dflags = dflags}) l_down
  | dopt dflag dflags = thing_inside down l_down >> return ()
  | otherwise	      = return ()

getDOptsRn :: RnM d DynFlags
getDOptsRn (RnDown { rn_dflags = dflags}) l_down
   = return dflags
\end{code}


%================
\subsubsection{Source location}
%=====================

\begin{code}
pushSrcLocRn :: SrcLoc -> RnM d a -> RnM d a
pushSrcLocRn loc' m down l_down
  = m (down {rn_loc = loc'}) l_down

getSrcLocRn :: RnM d SrcLoc
getSrcLocRn down l_down
  = return (rn_loc down)
\end{code}

%================
\subsubsection{The finder and home symbol table}
%=====================

\begin{code}
getHomeIfaceTableRn :: RnM d HomeIfaceTable
getHomeIfaceTableRn down l_down = return (rn_hit down)

getTypeEnvRn :: RnM d (Name -> Maybe TyThing)
getTypeEnvRn down l_down = return (rn_done down)

extendTypeEnvRn :: NameEnv TyThing -> RnM d a -> RnM d a
extendTypeEnvRn env inside down l_down
  = inside down{rn_done=new_rn_done} l_down
  where new_rn_done = \nm -> lookupNameEnv env nm `seqMaybe` rn_done down nm
\end{code}

%================
\subsubsection{Name supply}
%=====================

\begin{code}
getNameSupplyRn :: RnM d NameSupply
getNameSupplyRn rn_down l_down
  = readIORef (rn_ns rn_down)

setNameSupplyRn :: NameSupply -> RnM d ()
setNameSupplyRn names' (RnDown {rn_ns = names_var}) l_down
  = writeIORef names_var names'

getUniqRn :: RnM d Unique
getUniqRn (RnDown {rn_ns = names_var}) l_down
 = readIORef names_var >>= \ ns ->
   let
     (us1,us') = splitUniqSupply (nsUniqs ns)
   in
   writeIORef names_var (ns {nsUniqs = us'})	>>
   return (uniqFromSupply us1)
\end{code}

%================
\subsubsection{  Module}
%=====================

\begin{code}
getModuleRn :: RnM d Module
getModuleRn (RnDown {rn_mod = mod}) l_down
  = return mod

setModuleRn :: Module -> RnM d a -> RnM d a
setModuleRn new_mod enclosed_thing rn_down l_down
  = enclosed_thing (rn_down {rn_mod = new_mod}) l_down
\end{code}


%************************************************************************
%*									*
\subsection{Plumbing for rename-source part}
%*									*
%************************************************************************

%================
\subsubsection{  RnEnv}
%=====================

\begin{code}
getLocalNameEnv :: RnMS LocalRdrEnv
getLocalNameEnv rn_down (SDown {rn_lenv = local_env})
  = return local_env

getGlobalNameEnv :: RnMS GlobalRdrEnv
getGlobalNameEnv rn_down (SDown {rn_genv = global_env})
  = return global_env

getGlobalAvails :: RnMS AvailEnv
getGlobalAvails  rn_down (SDown {rn_avails = avails})
  = return avails

setLocalNameEnv :: LocalRdrEnv -> RnMS a -> RnMS a
setLocalNameEnv local_env' m rn_down l_down
  = m rn_down (l_down {rn_lenv = local_env'})

getFixityEnv :: RnMS LocalFixityEnv
getFixityEnv rn_down (SDown {rn_fixenv = fixity_env})
  = return fixity_env

setFixityEnv :: LocalFixityEnv -> RnMS a -> RnMS a
setFixityEnv fixes enclosed_scope rn_down l_down
  = enclosed_scope rn_down (l_down {rn_fixenv = fixes})
\end{code}

%================
\subsubsection{  Mode}
%=====================

\begin{code}
getModeRn :: RnMS RnMode
getModeRn rn_down (SDown {rn_mode = mode})
  = return mode

setModeRn :: RnMode -> RnMS a -> RnMS a
setModeRn new_mode thing_inside rn_down l_down
  = thing_inside rn_down (l_down {rn_mode = new_mode})
\end{code}


%************************************************************************
%*									*
\subsection{Plumbing for rename-globals part}
%*									*
%************************************************************************

\begin{code}
getIfacesRn :: RnM d Ifaces
getIfacesRn (RnDown {rn_ifaces = iface_var}) _
  = readIORef iface_var

setIfacesRn :: Ifaces -> RnM d ()
setIfacesRn ifaces (RnDown {rn_ifaces = iface_var}) _
  = writeIORef iface_var ifaces
\end{code}
