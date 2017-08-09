{-# LANGUAGE CPP, TupleSections, ScopedTypeVariables, RecordWildCards,
             NamedFieldPuns, ViewPatterns #-}
module ParUpsweep
  ( MakeTaskPriority
  , zeroMakeTaskPriority, makeTaskPriority, infiniteMakeTaskPriority
  , IsBoot(..), BuildModule(..), MakePipeline(..), MakeTask(..)
  , hscSourceToIsBoot, buildModuleModuleName, mkBuildModule
  , MakeQueue, mkMakeQueue, nextMakeTask, completeTask, failBuildModule
  , queueMakeTask
  , ParUpsweepMessage(..), LogData(..), ParUpsweepState, ParUpsweepM
  , CompilationCancelled(..)
  , runParUpsweepM, monitorChanUntilModuleComplete , puDoModuleSummaries
  , mkParUpsweepState, puTakeMVarAndContinue
  ) where

import BasicTypes
import Maybes hiding (Succeeded, Failed)
import Util
import Panic
import Module
import ErrUtils
import Outputable
import SrcLoc
import HscTypes
import DynFlags

import Control.Concurrent.Chan
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Strict as Strict
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map.Lazy as LazyMap
import qualified Data.Map.Strict as Map
import Data.Monoid hiding ((<>))
import Data.Ord
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable

#include "HsVersions.h"

-- | An estimate of how highly we should prioritize completion of a @MakeTask@.
-- Higher values will be prioritized ahead of lower values. Construct with
-- @zeroMakeTaskPriority@, @makeTaskPriority@ and @infiniteMakeTaskPriority@.
data MakeTaskPriority = MakeTaskPriority Int | MTP_Infinite
  deriving (Eq, Show)

instance Ord MakeTaskPriority where
  MTP_Infinite `compare` MTP_Infinite = EQ
  MTP_Infinite `compare` _ = GT
  _ `compare` MTP_Infinite = LT
  MakeTaskPriority x `compare` MakeTaskPriority y = x `compare` y

zeroMakeTaskPriority :: MakeTaskPriority
zeroMakeTaskPriority = MakeTaskPriority 0

makeTaskPriority :: Int -> MakeTaskPriority
makeTaskPriority = MakeTaskPriority

infiniteMakeTaskPriority :: MakeTaskPriority
infiniteMakeTaskPriority = MTP_Infinite

sumMakeTaskPrioritys :: MakeTaskPriority -> MakeTaskPriority -> MakeTaskPriority
sumMakeTaskPrioritys mv1 mv2
  | MTP_Infinite <- mv1 = MTP_Infinite
  | MTP_Infinite <- mv2 = MTP_Infinite
  | MakeTaskPriority x <- mv1, MakeTaskPriority y <- mv2 =
      MakeTaskPriority (x + y)

maxMakeTaskPrioritys :: MakeTaskPriority -> MakeTaskPriority -> MakeTaskPriority
maxMakeTaskPrioritys mv1 mv2
  | MTP_Infinite <- mv1 = MTP_Infinite
  | MTP_Infinite <- mv2 = MTP_Infinite
  | MakeTaskPriority x <- mv1, MakeTaskPriority y <- mv2 =
      MakeTaskPriority (x `max` y)

addMakeTaskPriorityConcurrently :: MakeTaskPriority
                                -> MakeTaskPriority
                                -> MakeTaskPriority
addMakeTaskPriorityConcurrently = maxMakeTaskPrioritys

addMakeTaskPrioritySequentially :: MakeTaskPriority
                                -> MakeTaskPriority
                                -> MakeTaskPriority
addMakeTaskPrioritySequentially = sumMakeTaskPrioritys

-- | 'Bool' indicating if a module is a boot module or not.  We need to treat
-- boot modules specially when building compilation graphs, since they break
-- cycles.  Regular source files and signature files are treated equivalently.
data IsBoot = IsBoot | NotBoot
    deriving (Ord, Eq, Show, Read)

-- | Tests if an 'HscSource' is a boot file, primarily for constructing
-- elements of 'BuildModule'.
hscSourceToIsBoot :: HscSource -> IsBoot
hscSourceToIsBoot HsBootFile = IsBoot
hscSourceToIsBoot _ = NotBoot

-- A Module and whether it is a boot module.
data BuildModule = BuildModule ModuleName IsBoot
  deriving (Eq, Ord)

instance Outputable BuildModule where
  ppr (BuildModule mn ib) =
    ppr mn <> (if ib ==IsBoot then text "-boot" else empty)

-- Retrieves the @ModuleName@ from a @BuildModule@
buildModuleModuleName :: BuildModule -> ModuleName
buildModuleModuleName (BuildModule mn _) = mn

mkBuildModule :: ModSummary -> BuildModule
mkBuildModule ms =
  BuildModule (ms_mod_name ms) (hscSourceToIsBoot . ms_hsc_src $ ms)

-- | A task that can be scheduled by a @MakeQueue@.
data MakeTask = MakeTask BuildModule MakePipeline
  deriving (Eq, Ord)

instance Outputable MakeTask where
  ppr (MakeTask bm mp) = ppr bm <+> char ':' <+> ppr mp

-- | A stage in the compilation of a module. The implementation depends on
-- the @Ord@, @Bounded@ and @Enum@ instances.
data MakePipeline
  = MP_Parse
  -- ^ The compilation of a module up until the completion of 'hscParse'
  | MP_Typecheck
  -- ^ The compilation of a module up until the completion of 'hscDesugar'
  | MP_Simplify
  -- ^ The compilation of a module up until the completion of 'hscSimplify'
  | MP_CodeGen
  -- ^ The complete compilation of a module
  deriving (Eq, Ord, Show, Bounded, Enum)

instance Outputable MakePipeline where
  ppr x = text $ case x of
    MP_Parse -> "parse"
    MP_Typecheck -> "typecheck"
    MP_Simplify -> "simplify"
    MP_CodeGen -> "codegen"

-- | An abstract data type created by @mkMakeQueu@ from a list of @MakeTask@s
-- each with a @MakeTaskPriority@ and a list of dependent @MakeTask@s.
-- Operations supported are:
-- * @nextMakeTask@ to extract the next task to run
-- * @completeTask@ to notify the queue that a task is complete so that other
--   tasks dependent on it may be returned by @nextMakeTask@.
-- * @failBuildModule@ to notify the queue that a build module has failed, so
--   that other tasks dependent on it can be failed.
-- * @queueMakeTask@ to add MakeTasks and dependencies to the queue that were
--   not known at construction time.
-- TODO DOUG: The inconsistency of these operation names is gross, fix that.
data MakeQueue = MakeQueue
  { mq_pqueue :: !(Set (Down MakeTaskPriority, MakeTask))
  -- ^ The set of tasks that have no unsatisfied dependencies, and so can be
  -- returned from @nextMakeTask@.
  , mq_waiting_to_queue :: !(Map MakeTask (MakeTaskPriority, Set MakeTask))
  -- ^ The collection of tasks, and their priorities and dependencies, that do
  -- have unsatisfied dependencies. The set of dependencies of a task is always
  -- nonempty.
  , mq_task_dependants :: !(Map MakeTask (Set MakeTask))
  -- ^ An index of dependants of a task. 'mq_task_dependants ! mt' Is the set
  -- of tasks that depend on 'mt'.
  }

-- | Takes a list of tasks each with a priority, and a list of dependencies
-- and constructs a MakeQueue.
-- The implicit dependency graph should be acyclic, and for any
-- 'MakeTask bm mp | mp > minBound', -- 'MakeTask bm (pred mp)' should be a
-- dependency. This is not checked. It's also not checked that dependencies are
-- in the graph, but they obviously must be. TODO DOUG: Check these in an
-- ASSERT.
-- postconditions:
-- 'mq_pqueue' contains all tasks with no dependences
-- 'mq_waiting_to_queue' contains all tasks with dependencies
-- for all 'mt' : 'mq_task_dependants ! mt' is exactly the set of MakeTasks that
-- depend on 'mt'
mkMakeQueue :: HasCallStack
  => [(MakeTask, MakeTaskPriority, [MakeTask])] -> MakeQueue
mkMakeQueue tasks = MakeQueue {..}
  where
    f (p1, s1) (p2, s2) = (p1 `max` p2, s1 `mappend` s2)
    all_tasks_map = Map.fromListWith f $ fold
      [ [(mt, ( p , Set.fromList dependencies))]
      | (mt, p, dependencies) <- tasks
      ]
    (unblocked_tasks_map, blocked_tasks_map) =
      Map.partition (\(_, s) -> null s) all_tasks_map
    mq_task_dependants =
      Map.fromListWith
        mappend
        [ (d, Set.singleton mt)
        | (mt, (_, dependencies)) <- Map.toList blocked_tasks_map
        , d <- toList dependencies
        ]
    -- Computing MakeTaskPriorities:
    -- We assume we have infinite parallelism available. Then the priority of a
    -- task is the the priority we were told, plus the maximum of the computed
    -- priority of our dependencies.
    mq_waiting_to_queue =
      LazyMap.mapWithKey add_dependant_costs blocked_tasks_map
      where
        add_dependant_costs mt (p, deps) =
          (p `addMakeTaskPrioritySequentially` dependant_costs, deps)
          where
            dependants =
              fromMaybe Set.empty . Map.lookup mt $ mq_task_dependants
            dependant_costs =
              foldl' addMakeTaskPriorityConcurrently zeroMakeTaskPriority
              [ p'
              | d <- toList dependants
              , let (p', _) = mq_waiting_to_queue Map.! d]
    mq_task_dependants_ok =
      all (`Map.member` all_tasks_map) $ Map.keys mq_task_dependants
    mq_pqueue = ASSERT(mq_task_dependants_ok) Map.foldMapWithKey
      (\k (p, _) -> Set.singleton (Down p, k)) unblocked_tasks_map

-- | Add another @MakeTask@ to a @MakeQueue@. This is used when we discover
-- additional dependencies during compilation. In practise the new MakeTask is
-- one that has already been dequeued in @nextMakeTask@, but which we discovered
-- we could not complete yet
queueMakeTask :: MakeTask
              -> MakeTaskPriority
              -> [MakeTask]
              -> MakeQueue
              -> MakeQueue
queueMakeTask mt p mts MakeQueue {..} =
  case () of
    _ | null mts -> MakeQueue
        { mq_pqueue = Set.insert (Down p, mt) mq_pqueue, ..}
      | otherwise -> MakeQueue
         { mq_task_dependants =
             foldr (Map.adjust (Set.insert mt)) mq_task_dependants mts
         , mq_waiting_to_queue =
            Map.insert mt (p, Set.fromList mts) mq_waiting_to_queue
         , ..
         }

-- | Dequeue the next @MakeTask@ from a @MakeQueue@. We don't have an
-- operation to check for an empty @MakeQueue@, and a @Nothing@ result here
-- doesn't mean the queue is empty, just that any tasks have unsatisfied
-- dependencies. We currently drop the queue once we've done everything
-- we put in, but a 'nullMakeQueue' operation may well be a good idea.
nextMakeTask :: MakeQueue -> (Maybe MakeTask, MakeQueue)
nextMakeTask mq =
  maybe (Nothing, mq) (\((_, mt), new_q) -> (Just mt, mq {mq_pqueue = new_q})) .
  Set.minView . mq_pqueue $
  mq

-- | Notify a @MakeQueue@ that a @MakeTask@ is complete, allowing tasks
-- dependent on the completed tasks to be returned by calls to
-- @nextMakeTask@.
completeTask :: MakeTask -> MakeQueue -> MakeQueue
completeTask mt@(MakeTask bm _) MakeQueue { mq_task_dependants = td
                                           , mq_pqueue = pq
                                           , mq_waiting_to_queue = wq
                                           , ..} =
  -- first we remove mt, and anything that must have completed for mt to have
  -- completed, from mq_task_dependents. This makes us robust to receiving, for
  -- example:
  -- completeTask (MakeTask m MP_CodeGen)
  -- , having never received
  -- completeTask (MakeTask m MP_Parse)
  --
  -- Then we take the dependants of anything we removed, and remove mt (and
  -- anything that must have completed for mt to complete) from those
  -- dependants' dependencies. If anything has no dependencies left, we move
  -- it to mq_pqueue
  let (tasks_to_possibly_unblock, mq_task_dependants) =
        -- we remove any MakeTasks from mq_task_dependants that must have been
        -- completed, including mt. The dependants of those tasks are
        -- tasks_to_possibly_unblock
        let (td1, td2) = Map.spanAntitone (< MakeTask bm minBound) td
            (td3, td4) = Map.spanAntitone (<= mt) td2
        in (fold td3, td1 `mappend` td4)
      -- we remove mk (and anything that must have completed for mt to complete)
      -- from the dependencies of tasks_to_possibly_unblock. Anything with
      -- no dependencies remaining moves to tasks_to_queue
      (mq_waiting_to_queue, tasks_to_queue) =
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
                  return (Set.singleton (Down p, dependent_task))
            for_ mb_queueing_task Strict.tell
            return wq''
            where
              remove_dependency (p, s) =
                let (s1, s2) = Set.spanAntitone (< MakeTask bm minBound) s
                    (_, s3) = Set.spanAntitone (<= mt) s2
                    s' = s1 `mappend` s3
                -- return Nothing if there are no more dependencies
                in guard (not . null $ s') *> pure (p, s')
      mq_pqueue = pq `mappend` tasks_to_queue
  in MakeQueue {..}

-- | Notify a @MakeQueue@ that a @BuildModule@ has failed, returning a
-- new queue and a set of other @BuildModule@s that have been removed from
-- the queue due to depending on the original (failed) @BuildModule@.
-- TODO DOUG: This is a weird asymmetry, shouldn't this use @MakeTask@s
-- as well?
failBuildModule :: BuildModule -> MakeQueue -> (Set BuildModule, MakeQueue)
failBuildModule bm MakeQueue { mq_task_dependants = td
                             , mq_waiting_to_queue = wq
                             , ..
                             } =
  let (mq_task_dependants, tasks_to_fail) =
        let (td1, td2) = Map.spanAntitone (< MakeTask bm minBound) td
            (td3, td4) = Map.spanAntitone (<= MakeTask bm maxBound) td2
        in (td1 `mappend` td4, fold td3)
      mq_waiting_to_queue = foldr Map.delete wq $ tasks_to_fail
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
-- ParUpsweepM
-- A State monad that manages a compilation of a module graph by maintaining
-- a @MakeQueue@, some per-@BuildModule@ state. It listens for progress as
-- @ParUpsweepMessage@s on a @Chan@.


-- | When worker threads log, they send a @PUM_Log@ messages with @LogData@s
-- inside them, then the main thread logs those messages at an appropriate
-- time.
data LogData =
  LogData !DynFlags !WarnReason !Severity !SrcSpan !PprStyle !MsgDoc

-- | As compilation progresses, we maintain the progress of each @BuildModule@.
data BuildModuleProgress
  = WaitingToStart MakePipeline (MVar Bool)
  -- ^ The @BuildModule@ is blocked on @takeMVar@ on this @MVar@. If we
  -- @putMVar@ @True@ it will continue into the @MakePipeline@ stage indicated.
  -- If we put @False@ it will throw a @CompilationCancelled@, to be caught in
  -- @parUpsweep
  | WorkingOn MakePipeline
  -- ^ A worker thread is working on this stage of the @BuildModule@.
  -- DOUG TODO: Perhaps we should store the @ThreadId@ here, so we can @throwTo@
  -- to cancel it in some failure cases.
  | Finished SuccessFlag
  -- ^ The @BuildModule@ has completed with this result.

instance Outputable BuildModuleProgress where
  ppr (WaitingToStart mp _) = text "WaitingToStart" <+> ppr mp
  ppr (WorkingOn mp) = text "WorkingOn" <+> ppr mp
  ppr (Finished sf) = text "Finished" <> ppr sf

-- | The per-@BuildModule@ state we maintain.
data BuildModuleState = BuildModuleState (Seq LogData) BuildModuleProgress

-- | The state type for @ParUpsweepM@
data ParUpsweepState = ParUpsweepState
  { pu_make_queue :: MakeQueue
  -- ^ The current @MakeQueue@
  , pu_module_data :: Map BuildModule BuildModuleState
  -- ^ The current per-@BuildModule@ state
  , pu_free_jobs :: Int
  -- ^ The number of worker threads we could unblock if we had tasks for them.
  }

-- | Create an initial ParUpsweepState from a graph of MakeTasks(see
-- @mkMakeQueue@). Also return a map of initial @MVar@s, each module should wait
-- it's @MVar@ before beginning.
mkParUpsweepState :: [(MakeTask, MakeTaskPriority, [MakeTask])]
  -> IO (ParUpsweepState, Map BuildModule (MVar Bool))
mkParUpsweepState mk_task_graph = do
  bm_to_mvar_map <- Map.fromList <$> sequence
    [ (bm,) <$> newEmptyMVar
    | bm <- toList . Set.fromList $
      [ bm | ((MakeTask bm _), _, _) <- mk_task_graph]
    ]
  let pu_make_queue = mkMakeQueue mk_task_graph
      pu_module_data =
        fmap (\mv -> BuildModuleState mempty (WaitingToStart minBound mv))
          bm_to_mvar_map
      pu_free_jobs = 0
  return (ParUpsweepState{..}, bm_to_mvar_map)

-- | Worker threads send these messages to the main thread, which it uses to
-- update it's state. Most messages contain an @MVar Bool@, in those cases
-- the worker is waiting on that @MVar@.
data ParUpsweepMessage
  = PUM_Log !BuildModule !LogData
  -- ^ The log_action in the worker threads @DynFlags@ will send this message
  -- to the main thread.
  | PUM_Parsed !BuildModule !(MVar Bool)
  -- ^ This @BuildModule@ has finished parsing.
  | PUM_Typechecked !BuildModule !(MVar Bool)
  -- ^ This @BuildModule@ has finished typechecking. Note that we may receive
  -- this having not received an earlier corresponding PUM_Parsed message.
  | PUM_Simplified !BuildModule !(MVar Bool)
  -- ^ This @BuildModule@ has finished simplifying. Note that we may receive
  -- this having not received an earlier corresponding PUM_Typechecked message.
  | PUM_Finished !BuildModule !SuccessFlag
  -- ^ This @BuildModule@ has finished. Note that we may receive
  -- this having not received an earlier corresponding PUM_Simplified message.
  | PUM_AdHocWait !BuildModule MakeTaskPriority [MakeTask] !(MVar Bool)
  -- ^ While working on this @BuildModule@ the worker thread discovered it had
    -- additional dependencies.

-- | The Upsweep Monad
type ParUpsweepM a = Strict.StateT ParUpsweepState IO a

-- | A helper function to update a @MakeQueue@ inside a @ParUpsweepState@
modMakeQueue :: (MakeQueue -> MakeQueue) -> ParUpsweepState -> ParUpsweepState
modMakeQueue f ParUpsweepState{..} =
  ParUpsweepState {pu_make_queue = f pu_make_queue, ..}

-- | A helper function to retrieve a @BuildModuleState@ from a
-- @ParUpsweepState@. This will throw if called on a BuildModule that's not
-- being tracked.
getBuildModuleState :: HasCallStack
  => BuildModule -> ParUpsweepState -> BuildModuleState
getBuildModuleState bm ParUpsweepState {pu_module_data} =
  pu_module_data Map.! bm

-- | A helper function to set a @BuildModuleState@ inside a @ParUpsweepState@
putBuildModuleState :: BuildModule
                    -> BuildModuleState
                    -> ParUpsweepState
                    -> ParUpsweepState
putBuildModuleState bm bms p@ParUpsweepState {pu_module_data} = p
  {pu_module_data = Map.insert bm bms pu_module_data}

-- | A helper function to modify a @BuildModuleState@ inside a
-- @ParUpsweepState@. This will throw if called on a BuildModule that's not
-- being tracked.
modBuildModuleState :: HasCallStack
  => BuildModule
  -> (BuildModuleState -> BuildModuleState)
  -> ParUpsweepState
  -> ParUpsweepState
modBuildModuleState bm f pu =
  let bms' =  f . getBuildModuleState bm $ pu
  in putBuildModuleState bm bms' pu

-- | A helper function to retrieve a @BuildModuleState@ from a
-- @ParUpsweepState@. This will throw if called on a BuildModule that's not
-- being tracked.
getBuildModuleProgress :: HasCallStack
  => BuildModule -> ParUpsweepState -> BuildModuleProgress
getBuildModuleProgress bm pu =
  let BuildModuleState _ progress = getBuildModuleState bm pu
  in progress

-- | A helper function to set a @BuildModuleProgress@ inside a
-- @ParUpsweepState@. This will throw if called on a BuildModule that's not
-- being tracked.
putBuildModuleProgress :: HasCallStack
  => BuildModule -> BuildModuleProgress -> ParUpsweepState -> ParUpsweepState
putBuildModuleProgress bm bmp = modBuildModuleProgress bm $ const bmp

-- | A helper function to modify a @BuildModuleProgress@ inside a
-- @ParUpsweepState@. This will throw if called on a BuildModule that's not
-- being tracked.
modBuildModuleProgress :: HasCallStack
  => BuildModule
  -> (BuildModuleProgress -> BuildModuleProgress)
  -> ParUpsweepState
  -> ParUpsweepState
modBuildModuleProgress bm f = modBuildModuleState bm $
  \(BuildModuleState logs progress) -> BuildModuleState logs (f progress)

-- | A helper function to modify a @ParUpsweepState@ by increasing
-- the number of free jobs.

addFreeJobs :: Int -> ParUpsweepState -> ParUpsweepState
addFreeJobs n pu = pu {pu_free_jobs = pu_free_jobs pu + n}

-- | When a @MakeTask@ completes it is either finished with a @SuccessFlag@ or
-- waiting on an @MVar Bool@ to start another @MakePipeline@ stage.
-- This function updates the monadic state and starts another task with
-- @puStartTasks@.
-- TODO DOUG: Figure out and add -ddump-make logging
puCompleteTask :: HasCallStack
  => BuildModule
  -> Either SuccessFlag (MakePipeline, MVar Bool)
  -> ParUpsweepM ()
puCompleteTask bm new_progress = do
  -- gross
  let pprable_new_progress = fmap (fmap (const ())) new_progress
  old_progress <- Strict.gets (getBuildModuleProgress bm)
  Strict.modify' $ putBuildModuleProgress bm $
    either Finished (uncurry WaitingToStart) new_progress
  -- TODO DOUG: This case statement has got a bit out of hand, look at
  -- refactoring it.
  case (old_progress, new_progress) of
    (Finished Succeeded, _) ->
      pprPanic "puCompleteTask" $
      text "completed after success" <+> ppr (bm, pprable_new_progress)
    (Finished Failed, Left Succeeded) ->
      pprPanic "puCompleteTask" $
      text "finished successfully after failure" <+> ppr bm
    (WaitingToStart old_mp mvar, Left Failed) -> do
      _ <- -- pprTrace "puCompleteTask"
           -- (text "Failing" <+> ppr (MakeTask bm old_mp)) $
      -- The only way we can get here is if this mvar has already been put, but
      -- let's be safe TODO DOUG: really? I don't think it can be put without
      -- progress going to Failed as well. I'll revisit this later
        liftIO $ tryPutMVar mvar False
      fail_build_module bm old_mp
    (WaitingToStart{}, _) ->
      pprPanic "puCompleteTask" $
        text "Completing a task that is waiting to start" <+>
        ppr (bm, old_progress, pprable_new_progress)
    (Finished Failed, Left Failed) -> return ()
    (Finished Failed, Right (_, mvar)) -> do
      --  This can happen if we marked the build module as failed in
      -- fail_make_task
      _ <- liftIO $ tryPutMVar mvar False
      return ()
    (WorkingOn old_mp, Left Failed) -> do
      -- This is a normal case
      -- pprTrace "puCompleteTask"
      -- (text "Failing" <+> ppr (MakeTask bm old_mp)) $
        fail_build_module bm old_mp
    (WorkingOn _old_mp, Left Succeeded) ->
      -- This is a normal case
      -- pprTrace "puCompleteTask" (text "Finishing" <+> ppr bm) $
      Strict.modify' $ modMakeQueue $ completeTask $ MakeTask bm maxBound
    (WorkingOn old_mp, Right (new_mp, _mvar)) ->
      -- This is a normal case.
      -- we may have done more than we were asked to,
      -- so we complete (pred new_mp) here
      -- pprTrace "puCompleteTask"
      -- (text "Completing" <+> ppr (MakeTask bm (pred new_mp)) $
        ASSERT(new_mp >= old_mp) Strict.modify' $
          modMakeQueue $ completeTask $ MakeTask bm (pred new_mp)
  Strict.modify' $ addFreeJobs 1
  puStartTasks
  where
    -- mark a build module and everything (that hasn't finished) that
    -- transitively depends on any of it's MakeTasks as Failed.
    -- TODO DOUG: This is perhaps to coarse, why not allow MakeTasks that depend
    -- on earlier phases to run?
    fail_build_module bm _mp  = do
      old_queue <- Strict.gets pu_make_queue
      let (failed_dependants_set, new_queue) =
            failBuildModule bm old_queue
      Strict.modify $ modMakeQueue $ const new_queue
      for_ failed_dependants_set $ \bm' -> do
        progress <- Strict.gets $ getBuildModuleProgress bm'
        case progress of
          WaitingToStart _mp mvar -> do
            _ <- -- pprTrace "puCompleteTask"
                 -- (text "Failing" <+> ppr (MakeTask bm' mp)) $
              liftIO $ tryPutMVar mvar False
            return ()
          --  we could potentially throw an exception to the working thread
          -- here:
          WorkingOn _ -> return ()
          _ -> return ()
        Strict.modify' $ modBuildModuleProgress bm' (const $ Finished Failed)

-- | When a @MakeTask@ completes it is either finished with a @SuccessFlag@ or
-- waiting on an @MVar Bool@ to start another @MakePipeline@ stage.
-- This function updates the monadic state and starts another task with
-- @puStartTask@.
-- DOUG TODO: Figure out and add -ddump-make logging
parUpsweepHandleMessage :: HasCallStack
  => LogAction
  -- ^ If we receive a log the current @BuildModule@, we use this @LogAction@ on
  -- it
  -> BuildModule
  -- ^ The current @BuildModule@. This is only used to determine how to treat
  -- logs
  -> ParUpsweepMessage
  -- ^ The message to handle.
  -> ParUpsweepM ()
parUpsweepHandleMessage log_action current_bm msg = do
  case msg of
    PUM_Log bm ld@(LogData df wr sev ss st d) -> do
      -- If this is a message for the current module, log immediately.
      -- Otherwise, snoc it into the appropriate @BuildModuleState@ whence it
      -- will be logged once that @BuildModule@ becomes current.
      if bm == current_bm
        then liftIO $ log_action df wr sev ss st d
        else Strict.modify' $
          modBuildModuleState bm $
            \(BuildModuleState logs progress) ->
              BuildModuleState (logs Seq.|> ld) progress
    PUM_Parsed bm mv -> do
      puCompleteTask bm $ Right (MP_Typecheck, mv)
    PUM_Typechecked bm mv -> do
      puCompleteTask bm $ Right (MP_Simplify, mv)
    PUM_Simplified bm mv -> do
      puCompleteTask bm $ Right (MP_CodeGen, mv)
    PUM_Finished bm sf -> do
      puCompleteTask bm $ Left sf
    PUM_AdHocWait bm p mts mv -> do
      mod_data <- Strict.gets pu_module_data
      WorkingOn mp <- Strict.gets $ getBuildModuleProgress bm
      let mts' = [mt | mt@(MakeTask bm mp) <- mts, case mod_data Map.! bm of
                     (BuildModuleState _ (WorkingOn mp'))
                       | mp' <= mp -> True
                     (BuildModuleState _ (WaitingToStart mp' _))
                       | mp' <= mp -> True
                     _ -> False]
      Strict.modify' $
        putBuildModuleProgress bm (WaitingToStart mp mv)
        . modMakeQueue (queueMakeTask (MakeTask bm mp) p mts')
        . addFreeJobs 1
      puStartTasks
      -- TODO DOUG: The commented code below is my work in progress refactor
      -- this to use puCompleteTask. Doesn't currently work because
      -- puCompleteTask takes the pred of the MakePipeline, expecting it to be
      -- at least larger than the modules current stage
      -- pu <- Strict.get
      -- let -- TODO DOUG: At least panic with a message here. It's "safe"
      --     -- because
      --     -- to receive a message the BuildModule must be working, hence in
      --     -- WorkingOn
      --     WorkingOn mp = getBuildModuleProgress bm pu
      --     mts' =
      --       [ mt
      --       | mt@(MakeTask bm mp) <- mts
      --       , let bmp = getBuildModuleProgress bm pu
      --             should_depend_on_this_build_module = case bmp of
      --               -- Here we filter the dependencies we were passed
      --               -- to exclude any that have progressed past what
      --               -- we need. DOUG TODO: We should sanity check
      --               -- for Failed tasks as well. (It can't happen without
      --               -- a bug though)
      --               WorkingOn mp' | mp' <= mp -> True
      --               WaitingToStart mp' _ | mp' <= mp -> True
      --               _ -> False
      --       , should_depend_on_this_build_module
      --       ]
      -- Strict.modify' $ modMakeQueue $ queueMakeTask (MakeTask bm mp) p mts'
      -- puCompleteTask bm (Right (mp, mv))

-- | Dequeue and start as many tasks as possible.
-- DOUG TODO: Figure out and add -ddump-make logging
puStartTasks :: HasCallStack => ParUpsweepM ()
puStartTasks = do
  pu@ParUpsweepState{..} <- Strict.get
  let -- A lazy list of (MakeTask, MVar Bool, MakeQueue).
      -- we take as many tasks as we can start, then set the MakeQueue in the
      -- state to be the MakeQueue of the last task added.
      startable_tasks mq =
        let (mb_mt, mq') = nextMakeTask mq
        -- Here we consider the MakeTask returned from mq
        in case mb_mt of
          -- In this case the BuildModule of the MakeTask has not
          -- progressed past the MakePipeliune of the MakeTask, so
          -- we cons the MakeTask to the list and recurse on mq'
          Just mt@(MakeTask bm mp)
            | WaitingToStart current_mp mvar <-
                getBuildModuleProgress bm pu
            , mp >= current_mp
            -> if mp == current_mp
              then (mt, mvar, mq') : startable_tasks mq'
              else pprPanic "startTasks" $ ppr bm <+>
              text "Time to start" <+> ppr mp <+> text "but waiting to start"
              <+> ppr current_mp
            | WorkingOn current_mp <- getBuildModuleProgress bm pu ->
              pprPanic "startTasks" $ ppr bm <+> text "Time to start"
              <+> ppr mp <+> text "but already working on" <+> ppr current_mp
          -- In this case, the BuildModule has progressed past the
          -- MakePipeline we are considering starting, so we discard this
          -- MakeTask and continue
          Just _ -> startable_tasks mq'
          -- There are no more unblocked MakeTasks in the queue
          Nothing -> []
      start_make_task (MakeTask bm mp) mvar = do
        Strict.modify' $ modBuildModuleProgress bm $ const $ WorkingOn mp
        -- pprTrace "startTasks" (text "starting" <+> ppr (MakeTask bm mp)) $
        liftIO $ putMVar mvar True
      (jobs_to_start, fromMaybe pu_make_queue . getLast -> pmq') =
        fold $ take pu_free_jobs
          -- We use a Seq because I'm scared the Monoid instance for [] might
          -- be inefficient... TODO DOUG: is it?
          [ (Seq.singleton $ start_make_task mt mvar, Last (Just mq))
          | (mt, mvar, mq) <- startable_tasks pu_make_queue]
      pfj' = pu_free_jobs - length jobs_to_start
  Strict.put pu{pu_make_queue = pmq', pu_free_jobs = pfj'}
  sequence_ jobs_to_start

-- | Handle messages from a @Chan ParUpsweepMessage@ until we receive a
-- @PUM_Finished@ for the given @BuildModule@.
-- called as 'for buildModules (monitorChanUntilModuleComplete log_action chan)'
-- perhaps we should take a list and move the 'for' in here.
monitorChanUntilModuleComplete :: LogAction
                               -> Chan ParUpsweepMessage
                               -> BuildModule
                               -> ParUpsweepM SuccessFlag
monitorChanUntilModuleComplete log_action chan bm = do
  BuildModuleState logs progress <- Strict.gets $ getBuildModuleState bm
  -- First, we do any logs that have accumulated before we got to this
  -- module
  liftIO $ for_ logs $ \(LogData df wr sv ss ps d) ->
    log_action df wr sv ss ps d
  Strict.modify' $ putBuildModuleState bm $ BuildModuleState Seq.empty progress
  go
  where
    -- check whether this module has finished (we won't get any more logs
    -- once it has), if it's finished, return it's result, otherwise
    -- handle the next message and recurse.
    go = do
      progress <- Strict.gets $ getBuildModuleProgress bm
      case progress of
        Finished r -> return r
        _ -> do
          liftIO (readChan chan) >>= parUpsweepHandleMessage log_action bm
          go

-- | Loop over each module in the compilation graph in order, printing
-- each log for a module before proceeding to the next. Returns @Just@
-- the @ModSummary@ for each successful module, and @Nothing@ for
-- failures
puDoModuleSummaries :: Chan ParUpsweepMessage
  -> LogAction
  -> [ModSummary]
  -> ParUpsweepM [Maybe ModSummary]
puDoModuleSummaries pum_chan log_action comp_graph = sequence
  [ do
    sf <- monitorChanUntilModuleComplete log_action pum_chan bm
    if succeeded sf
    then return (Just ms)
    else return Nothing
  | ms <- comp_graph
  , let bm = mkBuildModule ms
  ]

-- | This is an exception thrown inside parUpsweep worker threads to signal that
-- compilation was stopped or cancelled.
data CompilationCancelled = CompilationCancelled
  deriving (Show, Eq, Typeable)

instance Exception CompilationCancelled

-- | Take from the on the @MVar@ @Bool@. On @True@, continue. On @False@ throw
-- a @CompilationCancelled@
puTakeMVarAndContinue :: MVar Bool -> IO ()
puTakeMVarAndContinue mvar =
  takeMVar mvar >>= \should_continue ->
    unless should_continue $ throwIO CompilationCancelled

-- | Run an @ParUpsweepM@ given an initial @ParUpsweepState@ and the number of
-- parallel tasks to allow. Handles starting the first tasks.
runParUpsweepM :: ParUpsweepM a -> Int -> ParUpsweepState -> IO a
runParUpsweepM m n_jobs s = Strict.evalStateT go s
  where
    go = do
      Strict.modify' $ addFreeJobs n_jobs
      puStartTasks
      m
