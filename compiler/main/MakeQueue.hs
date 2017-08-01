{-# LANGUAGE CPP, TupleSections, ScopedTypeVariables, RecordWildCards, NamedFieldPuns, ViewPatterns #-}
module MakeQueue where

import BasicTypes
import Maybes hiding (Succeeded, Failed)
import Util
import Panic
import Module
-- import HscTypes
import ErrUtils
import Outputable
import SrcLoc
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Trans.Writer.Strict as Strict
import Data.Foldable
import Control.Monad
import qualified Control.Monad.Trans.State.Strict as Strict
import DynFlags
import Data.Ord
import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Monad.IO.Class
-- import Data.Maybe
import Data.Monoid hiding ((<>))
-- import Data.Traversable

#include "HsVersions.h"

-- data QueueItem = QueueItem Priority Module
--   deriving (Eq, Ord)

data MakeValue = MakeValue Int | MV_Infinite
  deriving (Eq, Show)

instance Ord MakeValue where
  MV_Infinite `compare` MV_Infinite = EQ
  MV_Infinite `compare` _ = GT
  _ `compare` MV_Infinite = LT
  MakeValue x `compare` MakeValue y = x `compare` y

zeroMakeValue :: MakeValue
zeroMakeValue = MakeValue 0

makeValue :: Int -> MakeValue
makeValue = MakeValue

infiniteMakeValue :: MakeValue
infiniteMakeValue = MV_Infinite

sumMakeValues :: MakeValue -> MakeValue -> MakeValue
sumMakeValues mv1 mv2
  | MV_Infinite <- mv1 = MV_Infinite
  | MV_Infinite <- mv2 = MV_Infinite
  | MakeValue x <- mv1, MakeValue y <- mv2 = MakeValue (x + y)

maxMakeValues :: MakeValue -> MakeValue -> MakeValue
maxMakeValues mv1 mv2
  | MV_Infinite <- mv1 = MV_Infinite
  | MV_Infinite <- mv2 = MV_Infinite
  | MakeValue x <- mv1, MakeValue y <- mv2 = MakeValue (x `max` y)

addMakeValueConcurrently :: MakeValue -> MakeValue -> MakeValue
addMakeValueConcurrently = maxMakeValues

addMakeValueSequentially :: MakeValue -> MakeValue -> MakeValue
addMakeValueSequentially = sumMakeValues

-- | 'Bool' indicating if a module is a boot module or not.  We need to treat
-- boot modules specially when building compilation graphs, since they break
-- cycles.  Regular source files and signature files are treated equivalently.
data IsBoot = IsBoot | NotBoot
    deriving (Ord, Eq, Show, Read)

-- A Module and whether it is a boot module.
data BuildModule = BuildModule ModuleName IsBoot
  deriving (Eq, Ord)

instance Outputable BuildModule where
  ppr (BuildModule mn ib) = ppr mn <> (if ib ==IsBoot then text "-boot" else empty)

buildModuleModuleName :: BuildModule -> ModuleName
buildModuleModuleName (BuildModule mn _) = mn

data MakeTask = MakeTask BuildModule MakePipeline
  deriving (Eq, Ord)

instance Outputable MakeTask where
  ppr (MakeTask bm mp) = ppr bm <+> char ':' <+> ppr mp

data MakePipeline = MP_Parse | MP_Typecheck | MP_Simplify | MP_CodeGen
  deriving (Eq, Ord, Show, Bounded, Enum)

instance Outputable MakePipeline where
  ppr x = text $ case x of
    MP_Parse -> "parse"
    MP_Typecheck -> "typecheck"
    MP_Simplify -> "simplify"
    MP_CodeGen -> "codegen"


type Priority = Down MakeValue
data MakeQueue = MakeQueue
  { mk_pqueue :: !(Set (Priority, MakeTask))
  , mk_waiting_to_queue :: !(Map MakeTask (Priority, Set MakeTask))
  , mk_task_dependants :: !(Map MakeTask (Set MakeTask))
  }

-- | Takes a list of tasks each with a priority, and a list of task dependencies
-- Each task MakeTask mod mp has dependencies on
-- the graph should be acyclic, but this is not checked
--
-- postconditions:
-- mk_pqueue contains all tasks with no dependences
-- mk_waiting_to_queue contains all tasks with dependencies
-- (mt, dependants) \el mk_task_dependants <=> \forall d \el dependants \exists (p, dependencies) : (d, (p, dependencies)) \el mk_waiting_to_queue \and mt \el dependencies

mkMakeQueue :: HasCallStack => [(MakeTask, MakeValue, [MakeTask])] -> MakeQueue
mkMakeQueue tasks = MakeQueue {..}
  where
    f (p1, s1) (p2, s2) = (p1 `max` p2, s1 `mappend` s2)
    all_tasks_map = Map.fromListWith f $ fold
      [ [(mt, ( p , Set.fromList dependencies))]
      | (mt, p, dependencies) <- tasks
      ]
    (unblocked_tasks_map, blocked_tasks_map) =
      Map.partition (\(_, s) -> null s) all_tasks_map
    mk_task_dependants =
      Map.fromListWith
        mappend
        [ (d, Set.singleton mt)
        | (mt, (_, dependencies)) <- Map.toList blocked_tasks_map
        , d <- toList dependencies
        ]
    mk_waiting_to_queue = LazyMap.mapWithKey add_dependant_costs blocked_tasks_map
      where
        add_dependant_costs mt (p, deps) =
          (Down $ p `addMakeValueSequentially` dependant_costs, deps)
          where
            dependants = fromMaybe Set.empty . Map.lookup mt $ mk_task_dependants
            dependant_costs = foldl' addMakeValueConcurrently zeroMakeValue
              [ p'
              | d <- toList dependants
              , let (Down p', _) = mk_waiting_to_queue Map.! d]
    mk_task_dependants_ok = all (`Map.member` all_tasks_map) $ Map.keys mk_task_dependants
    mk_pqueue = ASSERT (mk_task_dependants_ok) Map.foldMapWithKey (\k (p, _) -> Set.singleton (Down p, k)) unblocked_tasks_map

queueMakeTask :: MakeTask -> MakeValue -> [MakeTask] -> MakeQueue -> MakeQueue
queueMakeTask mt p mts MakeQueue {..} =
  case () of
    _ | null mts -> MakeQueue
        { mk_pqueue = Set.insert (Down p, mt) mk_pqueue, ..}
      | otherwise -> MakeQueue
         { mk_task_dependants =
             foldr (Map.adjust (Set.insert mt)) mk_task_dependants mts
         , mk_waiting_to_queue =
            Map.insert mt (Down p, Set.fromList mts) mk_waiting_to_queue
         , ..
         }


nextMakeTask :: MakeQueue -> (Maybe MakeTask, MakeQueue)
nextMakeTask mq =
  maybe (Nothing, mq) (\((_, mt), new_q) -> (Just mt, mq {mk_pqueue = new_q})) .
  Set.minView . mk_pqueue $
  mq

completeTask :: MakeTask -> MakeQueue -> MakeQueue
completeTask mt@(MakeTask mod _) MakeQueue { mk_task_dependants = td
                                           , mk_pqueue = pq
                                           , mk_waiting_to_queue = wq
                                           , ..} =
  -- first we remove mt, and anything that must have completed for mt to have
  -- completed, from mk_task_dependents. This makes us robust to receiving, for
  -- example:
  -- completeTask (MakeTask m MP_CodeGen)
  -- , having never received
  -- completeTask (MakeTask m MP_Parse)
  --
  -- Then we take the dependants of anything we removed, and remove mt (and
  -- anything that must have completed for mt to complete) from those
  -- dependants' dependencies. If anything has no dependencies left, we move
  -- it to mk_pqueue
  let (tasks_to_possibly_unblock, mk_task_dependants) =
        -- we remove any MakeTasks from mk_task_dependants that must have been
        -- completed, including mt. The dependants of those tasks are
        -- tasks_to_possibly_unblock
        let (td1, td2) = Map.spanAntitone (< MakeTask mod minBound) td
            (td3, td4) = Map.spanAntitone (<= mt) td2
        in (fold td3, td1 `mappend` td4)
      -- we remove mk (and anything that must have completed for mt to complete)
      -- from the dependencies of tasks_to_possibly_unblock. Anything with
      -- no dependencies left moves to tasks_to_queue
      (mk_waiting_to_queue, tasks_to_queue) =
        Strict.runWriter . foldM go wq $ tasks_to_possibly_unblock
        where
          go wq' dependent_task = do
            -- we can't use Map.updateLookupWithKey here because we wouldn't
            -- be able to tell whether the task was removed :(
            let mb_unqueued_task = Map.lookup dependent_task wq'
                wq'' = Map.update remove_dependency dependent_task wq'
                mb_queueing_task = do
                  -- check that dependent_task was removed
                  guard (dependent_task `Map.notMember` wq'')
                  (p, _) <- mb_unqueued_task
                  return (Set.singleton (p, dependent_task))
            for_ mb_queueing_task Strict.tell
            return wq''
            where
              remove_dependency (p, s) =
                let (s1, s2) = Set.spanAntitone (< MakeTask mod minBound) s
                    (_, s3) = Set.spanAntitone (<= mt) s2
                    s' = s1 `Set.union` s3
                -- return Nothing if there are no more dependencies
                in guard (not . null $ s') *> pure (p, s')
      mk_pqueue = pq `mappend` tasks_to_queue
  in MakeQueue {..}

failBuildModule :: BuildModule -> MakeQueue -> (Set BuildModule, MakeQueue)

failBuildModule bm MakeQueue { mk_task_dependants = td
                             , mk_waiting_to_queue = wq
                             , ..
                             } =
  let (mk_task_dependants, tasks_to_fail) =
        let (td1, td2) = Map.spanAntitone (< MakeTask bm minBound) td
            (td3, td4) = Map.spanAntitone (<= MakeTask bm maxBound) td2
        in (td1 `mappend` td4, fold td3)
      mk_waiting_to_queue = foldr Map.delete wq $ tasks_to_fail
      build_modules_to_fail = Set.map (\(MakeTask bm _) -> bm) tasks_to_fail
  in if null build_modules_to_fail
       then (Set.empty, MakeQueue {..})
       else foldl'
              (\(failed, mq) bm' ->
                 let (failed', mq') = failBuildModule bm' mq
                 in (failed `mappend` failed', mq'))
              (build_modules_to_fail, MakeQueue {..})
              build_modules_to_fail
-- =====================================



data LogData = LogData !DynFlags !WarnReason !Severity !SrcSpan !PprStyle !MsgDoc

data BuildModuleProgress
  = WaitingToStart MakePipeline (MVar Bool)
  | WorkingOn MakePipeline
  | Finished SuccessFlag

instance Outputable BuildModuleProgress where
  ppr (WaitingToStart mp _) = text "WaitingToStart" <+> ppr mp
  ppr (WorkingOn mp) = text "WorkingOn" <+> ppr mp
  ppr (Finished sf) = text "Finished" <> ppr sf

data BuildModuleState = BuildModuleState (Seq LogData) BuildModuleProgress

data ParUpsweepState = ParUpsweepState
  { pus_make_queue :: MakeQueue
  , pus_module_data :: Map BuildModule BuildModuleState
--  , pus_waiting_tasks :: Set (Priority, MakeTask)
  , pus_free_jobs :: Int
  }

data ParUpsweepMessage
  = PUM_Log !BuildModule !LogData
  | PUM_Parsed !BuildModule !(MVar Bool)
  | PUM_Typechecked !BuildModule !(MVar Bool)
  | PUM_Simplified !BuildModule !(MVar Bool)
  | PUM_Finished !BuildModule !SuccessFlag
  | PUM_AdHocWait !BuildModule MakeValue [MakeTask] !(MVar Bool)

type UpsweepM a = Strict.StateT ParUpsweepState IO a

-- makeQueuePopTasks :: Int -> Set BuildModule -> MakeQueue -> ([MakeTask], MakeQueue)
-- makeQueuePopTasks bms MakeQueue{..} =
--   let popped_task_with_priorities = [qi | qi@(p, mt) <- toList mk_pqueue, mt `Set.member` bms]
--       pq' = foldr Set.delete mk_pqueue popped_task_with_priorities
--       popped_tasks = [mt | (_, mt) <- popped_task_with_priorities]
--   in (popped_tasks, MakeQueue{mk_pqueue = pq', ..}

modBuildModuleState
  :: BuildModule
  -> (BuildModuleState -> BuildModuleState)
  -> ParUpsweepState
  -> ParUpsweepState
modBuildModuleState bm f pus =
  let bms' =  f . getBuildModuleState bm $ pus
  in putBuildModuleState bm bms' pus

modMakeQueue :: (MakeQueue -> MakeQueue) -> ParUpsweepState -> ParUpsweepState
modMakeQueue f ParUpsweepState{..} = ParUpsweepState {pus_make_queue = f pus_make_queue, ..}

getBuildModuleState :: HasCallStack => BuildModule -> ParUpsweepState -> BuildModuleState
getBuildModuleState bm ParUpsweepState {pus_module_data} = pus_module_data Map.! bm

putBuildModuleState :: BuildModule -> BuildModuleState -> ParUpsweepState -> ParUpsweepState
putBuildModuleState bm bms p@ParUpsweepState {pus_module_data} = p
  {pus_module_data = Map.insert bm bms pus_module_data}

getBuildModuleProgress :: BuildModule-> ParUpsweepState -> BuildModuleProgress
getBuildModuleProgress bm pus =
  let BuildModuleState _ progress = getBuildModuleState bm pus
  in progress

putBuildModuleProgress :: BuildModule-> BuildModuleProgress -> ParUpsweepState -> ParUpsweepState
putBuildModuleProgress bm bmp = modBuildModuleProgress bm $ const bmp

modBuildModuleProgress
  :: BuildModule
  -> (BuildModuleProgress -> BuildModuleProgress)
  -> ParUpsweepState
  -> ParUpsweepState
modBuildModuleProgress bm f = modBuildModuleState bm $
  \(BuildModuleState logs progress) -> BuildModuleState logs (f progress)

-- This always starts a task
puCompleteTask :: HasCallStack => BuildModule
               -> BuildModuleProgress
               -> UpsweepM ()
puCompleteTask bm new_progress = do
  old_progress <- Strict.gets (getBuildModuleProgress bm)
  Strict.modify' $ modBuildModuleProgress bm $ const new_progress
  case (old_progress, new_progress) of
    (_, WorkingOn {}) ->
      pprPanic "puCompleteTask" $ text "new_progress is WorkingOn" <+> ppr (bm, old_progress, new_progress)
    (Finished Succeeded, _) ->
      pprPanic "puCompleteTask" $ text "completed after success" <+> ppr (bm, new_progress)
    (Finished Failed, Finished Succeeded) ->
      pprPanic "puCompleteTask" $ text "finished successfully after failure" <+> ppr bm
    (WaitingToStart old_mp mvar, Finished Failed) -> do
      _ <- -- pprTrace "puCompleteTask" (text "Failing" <+> ppr (MakeTask bm old_mp)) $
      -- The only way we can get here is if this mvar has already been put, but let's be safe
        liftIO $ tryPutMVar mvar False
      fail_build_module bm old_mp
    (WaitingToStart{}, _) ->
      pprPanic "puCompleteTask" $ text "Completing a task that is waiting to start" <+> ppr (bm, old_progress, new_progress)
    --  This can happen if we marked the build module as failed in fail_make_task
    (Finished Failed, _) -> return ()
    (WorkingOn old_mp, Finished Failed) -> do
      -- pprTrace "puCompleteTask" (text "Failing" <+> ppr (MakeTask bm old_mp)) $
        fail_build_module bm old_mp
    (WorkingOn old_mp, WaitingToStart new_mp _mvar) ->
      -- This is the normal case
      -- pprTrace "puCompleteTask" (text "Completing" <+> ppr (MakeTask bm (pred new_mp))) $
      --  we may have done more than we were asked to, so we complete (pred new_mp) here
        ASSERT (new_mp > old_mp) Strict.modify' $ modMakeQueue $ completeTask $ MakeTask bm (pred new_mp)
    (WorkingOn _old_mp, Finished Succeeded) ->
      -- This is the normal case
      -- pprTrace "puCompleteTask" (text "Finishing" <+> ppr bm) $
      Strict.modify' $ modMakeQueue $ completeTask $ MakeTask bm maxBound
  startTasks 1
  where
    fail_build_module bm _mp  = do
      old_queue <- Strict.gets pus_make_queue
      let (failed_dependants_set, new_queue) =
            failBuildModule bm old_queue
      Strict.modify $ modMakeQueue $ const new_queue
      for_ failed_dependants_set $ \bm' -> do
        progress <- Strict.gets $ getBuildModuleProgress bm'
        case progress of
          WaitingToStart _mp mvar -> do
            _ <- -- pprTrace "puCompleteTask" (text "Failing" <+> ppr (MakeTask bm' mp)) $
              liftIO $ tryPutMVar mvar False
            return ()
          --  we could potentially throw an exception to the working thread here:
          WorkingOn _ -> return ()
          _ -> return ()
        Strict.modify' $ modBuildModuleProgress bm' (const $ Finished Failed)

parUpsweepHandleMessage
  :: HasCallStack
  => LogAction
  -> BuildModule
  -> ParUpsweepMessage
  -> UpsweepM ()
parUpsweepHandleMessage log_action bm msg = do
  case msg of
    PUM_Log bm' ld@(LogData df wr sev ss st d) -> do
      if bm' == bm
        then liftIO $ log_action df wr sev ss st d
        else Strict.modify' $ modBuildModuleState bm' $ \(BuildModuleState logs progress) -> BuildModuleState (logs Seq.|> ld) progress
    PUM_Parsed bm' mv -> do
      -- liftIO $ putStrLn $ "Doug:parUpsweepHandleMessage:PUM_Parsed:" ++ showPpr unsafeGlobalDynFlags bm'
      puCompleteTask bm' $ WaitingToStart MP_Typecheck mv
    PUM_Typechecked bm' mv -> do
      -- liftIO $ putStrLn $ "Doug:parUpsweepHandleMessage:PUM_Typechecked:" ++ showPpr unsafeGlobalDynFlags bm'
      puCompleteTask bm' $ WaitingToStart MP_Simplify mv
    PUM_Simplified bm' mv -> do
      -- liftIO $ putStrLn $ "Doug:parUpsweepHandleMessage:PUM_Simplified:" ++ showPpr unsafeGlobalDynFlags bm'
      puCompleteTask bm' $ WaitingToStart MP_CodeGen mv
    PUM_Finished bm' sf -> do
      -- liftIO $ putStrLn $ "Doug:parUpsweepHandleMessage:PUM_CodeGenned:" ++ showPpr unsafeGlobalDynFlags bm'
      puCompleteTask bm' $ Finished sf
    PUM_AdHocWait bm' p mts mv -> do
      mod_data <- Strict.gets pus_module_data
      WorkingOn mp <- Strict.gets $ getBuildModuleProgress bm'
      let mts' = [mt | mt@(MakeTask bm mp) <- mts, case mod_data Map.! bm of
                     (BuildModuleState _ (WorkingOn mp')) | mp' <= mp -> True
                     (BuildModuleState _ (WaitingToStart mp' _)) | mp' <= mp -> True
                     _ -> False]
      Strict.modify' $ putBuildModuleProgress bm' $ WaitingToStart mp mv
      Strict.modify' $ modMakeQueue $ queueMakeTask (MakeTask bm' mp) p mts'
      startTasks 1
  -- pus <- Strict.get
  -- liftIO $ putStrLn $ "queue: " ++ show (pus_make_queue pus)
  where
    -- bms_set_mvar bm x = Strict.modify' $ pusForBuildModule bm $ \(_,logs, sf) -> (Just x, logs, sf)
    -- bms_snoc_log bm x = Strict.modify' $ pusForBuildModule bm $ \(mv, logs, sf) -> (mv, logs Seq.|> x, sf)
    -- bms_remove_mvar bm = Strict.modify' $ pusForBuildModule bm $ \(_, logs, sf) -> (Nothing, logs, sf)
    -- bms_set_result bm sf = Strict.modify' $ pusForBuildModule bm $ \(mv, logs, _) -> (mv, logs, Just sf)
    -- bms_complete_task bm mp = do
    --   startTasks 1
    -- fail_task bm = do
    --   pmd <- Strict.gets pus_module_data
    --   let (mb_mvar, logs, _) = pmd Map.! bm
    --   liftIO $ for_ mb_mvar $ \x -> putMVar x False
    --   Strict.modify' $ pusForBuildModule bm $ const (Nothing, logs, Just Failed)

startTasks :: Int -> UpsweepM ()
startTasks n = do
  pus@ParUpsweepState{..} <- Strict.get
  let free_jobs = pus_free_jobs + n
      startable_tasks mq =
        let mk_bm_action bm mp mvar = do
              Strict.modify' $ modBuildModuleProgress bm $ const $ WorkingOn mp
              -- pprTrace "startTasks" (text "starting" <+> ppr (MakeTask bm mp)) $
              liftIO $ putMVar mvar True
            (mb_mt, mq') = nextMakeTask mq
        in case mb_mt of
          Just (MakeTask bm mp)
            | WaitingToStart current_mp mvar <-
                getBuildModuleProgress bm pus
            , mp >= current_mp
            -> if mp == current_mp
              then (mk_bm_action bm mp mvar, mq') : startable_tasks mq'
              else pprPanic "startTasks" $ ppr bm <+>
              text "Time to start" <+> ppr mp <+> text "but waiting to start"
              <+> ppr current_mp
            | WorkingOn current_mp <- getBuildModuleProgress bm pus ->
              pprPanic "startTasks" $ ppr bm <+> text "Time to start"
              <+> ppr mp <+> text "but already working on" <+> ppr current_mp
          Just _ -> startable_tasks mq'
          Nothing -> []
      (jobs_to_start, fromMaybe pus_make_queue . getLast -> pmq') =
        fold $ take free_jobs
          [ (Seq.singleton action , Last (Just mq))
          | (action, mq) <- startable_tasks pus_make_queue]
      pfj' = free_jobs - length jobs_to_start
  Strict.put pus{pus_make_queue = pmq', pus_free_jobs = pfj'}
  -- liftIO $ putStrLn $ "Doug:startTasks:starting " ++ show (length jobs_to_start) ++ " jobs"
  sequence_ jobs_to_start

monitorChanUntilModuleComplete :: LogAction -> Chan ParUpsweepMessage -> BuildModule -> UpsweepM SuccessFlag
monitorChanUntilModuleComplete log_action chan bm = do
  BuildModuleState logs progress <- Strict.gets $ getBuildModuleState bm
  liftIO $ for_ logs $ \(LogData df wr sv ss ps d) ->
    log_action df wr sv ss ps d
  Strict.modify' $ putBuildModuleState bm $ BuildModuleState Seq.empty progress
  go
  where
    go = do
      progress <- Strict.gets $ getBuildModuleProgress bm
      case progress of
        Finished r -> return r
        _ -> do
          liftIO (readChan chan) >>= parUpsweepHandleMessage log_action bm
          go

runUpsweepM :: UpsweepM a -> ParUpsweepState -> IO a
runUpsweepM m s = Strict.evalStateT (startTasks 0 *> m) s
