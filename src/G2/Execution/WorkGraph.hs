module G2.Execution.WorkGraph ( WorkGraph
                              , Status(..)
                              , WorkMap
                              , initGraph
                              , work) where

import qualified Data.Sequence as S
import qualified Data.HashMap.Strict as HM
import Data.Maybe

data Status = WorkNeeded | WorkSaturated | Split | Mergeable | Accept | Discard

type WorkMap a = HM.HashMap Int (S.Seq a, S.Seq a, S.Seq a) -- `a` objects with status WorkNeeded, WorkSaturated or Mergeable respectively
type WorkPlan = S.Seq Int

data WorkGraph a b = WorkGraph { wPlan :: WorkPlan -- ^ Sequence of indices that specifies order in which to choose next object to work on
                               , wMap :: WorkMap a -- ^ Map from index to set of objects belonging to that index
                               , work_func :: a -> b -> IO ([a], b, Status) -- ^ Function to perform work on an object
                               , merge_func :: S.Seq a -> S.Seq a -> b
                                    -> (S.Seq a, S.Seq a, Maybe Int, b) -- ^ Func to merge objects at specified idx
                               , add_idx_func :: Int -> a -> a -- ^ Function that adds index of object in the wMap to the object itself
                               , curr_idx :: Int
                               , max_idx :: Int -- ^ Used to ensure any new index generated is fresh
                               , context :: b -- ^ Any additional value that needs to maintain state between calls to merge_func or work_func
                               , logger :: Logger a } -- ^ Outputs String representation of Work if needed for debugging

initGraph :: a -> b
          -> (a -> b -> IO ([a], b, Status))
          -> (S.Seq a -> S.Seq a -> b -> (S.Seq a, S.Seq a, Maybe Int, b))
          -> (Int -> a -> a)
          -> (a -> String)
          -> WorkGraph a b
initGraph fstWork ctxt workFn mergeFn addIdxFn logWorkFn =
    let workMap = HM.singleton 0 (S.singleton fstWork, S.empty, S.empty)
        workPlan = S.singleton 0
    in WorkGraph {
          wPlan = workPlan
        , wMap = workMap
        , work_func = workFn
        , merge_func = mergeFn
        , add_idx_func = addIdxFn
        , curr_idx = 0
        , max_idx = 0
        , context = ctxt
        , logger = Logger logWorkFn 0 }


-- | Runs WorkGraph until workMap is empty and all objects have status `Accept` or `Discard`
work :: WorkGraph a b -> IO ([a], b)
work wGraph = do
    let (a, wGraph') = pickWork WorkNeeded wGraph
    case a of
        Just a' -> work' wGraph' a' []
        Nothing -> return ([], context wGraph')

work' :: WorkGraph a b -> a -> [a] -> IO ([a], b)
work' wGraph@(WorkGraph {
      work_func = workFunc
    , wMap = workMap
    , wPlan = workPlan
    , max_idx = maxIdx
    , curr_idx = idx
    , add_idx_func = addIdx
    , context = ctxt
    , logger = l }) a accepted = do
    -- l' <- outputLog l a
    (as, ctxt', status) <- workFunc a ctxt
    let wGraph' = wGraph { context = ctxt', logger = l }
    let (accepted', wGraph'') = case status of
            Accept -> (as ++ accepted, wGraph')
            Discard -> (accepted, wGraph')
            Mergeable ->
                let workMap' = addMergeable workMap idx (head as)
                in (accepted, wGraph' { wMap = workMap' })
            WorkSaturated ->
                let workMap' = addSaturated workMap idx (head as)
                in (accepted, wGraph' { wMap = workMap' })
            Split -> -- Add reduceds to newIdx, and add newIdx to front of workPlan to evaluate next
                let newIdx = maxIdx + 1
                    as' = map (addIdx newIdx) as
                    workMap' = HM.insert newIdx (S.fromList as', S.empty, S.empty) workMap
                    workPlan' = newIdx S.<| workPlan
                in (accepted, wGraph' { wMap = workMap', wPlan = workPlan', max_idx = newIdx, curr_idx = newIdx })
            WorkNeeded ->
                let workMap' = addWorkNeeded workMap idx as
                in (accepted, wGraph' { wMap = workMap' })
    let (a', wGraph''') = pickWork status wGraph''
    case a' of
        Just a'' -> work' wGraph''' a'' accepted'
        Nothing -> return (accepted', context wGraph''')

-- | Add object to the appropriate Seq in the set of objects for the specified index `idx`.
addMergeable :: WorkMap a -> Int -> a -> WorkMap a
addMergeable workMap idx a
    | Just (workNeeded, workSat, mergeable) <- HM.lookup idx workMap =
        let mergeable' = mergeable S.|> a
        in HM.insert idx (workNeeded, workSat, mergeable') workMap
    | otherwise = HM.insert idx (S.empty, S.empty, S.singleton a) workMap

addSaturated :: WorkMap a -> Int -> a -> WorkMap a
addSaturated workMap idx a
    | Just (workNeeded, workSat, mergeable) <- HM.lookup idx workMap =
        let workSat' = workSat S.|> a
        in HM.insert idx (workNeeded, workSat', mergeable) workMap
    | otherwise = HM.insert idx (S.empty, S.singleton a, S.empty) workMap

-- | Add list of objects `as` to appropriate Seq, at the specified index `idx`
addWorkNeeded :: WorkMap a -> Int -> [a] -> WorkMap a
addWorkNeeded workMap idx as
    | Just (workNeeded, workSat, mergeable) <- HM.lookup idx workMap =
        HM.insert idx (foldr (\s workNeeded' -> s S.<| workNeeded') workNeeded as,  workSat, mergeable) workMap
    | otherwise = HM.insert idx (S.fromList as, S.empty, S.empty) workMap

-- | Pick next object to work on, and remove it from the WorkGraph
pickWork  :: Status -> WorkGraph a b -> (Maybe a, WorkGraph a b)
pickWork status wGraph =
    case status of
        Accept -> pickWork' wGraph
        Discard -> pickWork' wGraph
        Mergeable -> pickWork' wGraph
        WorkSaturated ->  pickWork' wGraph
        Split -> switchIdxNoMerge wGraph
        WorkNeeded -> pickWork' wGraph

-- | Search set of objects in current index `idx` for next object to work on. If none available, merge all possible objects in current index
-- and pick object from the next index in wPlan to reduce, if any.
pickWork' :: WorkGraph a b -> (Maybe a, WorkGraph a b)
pickWork' wGraph@(WorkGraph { wMap = workMap, curr_idx = idx }) =
    let (maybeW, workMap') = switchWorkSameIdx idx workMap
        wGraph' = wGraph { wMap = workMap' }
    in case maybeW of
        Just next -> (Just next, wGraph')
        Nothing ->
            let (halt, wGraph'') = switchIdx wGraph'
            in if halt then (Nothing, wGraph'') else pickWork' wGraph''

-- | If an object `x` with index `idx` that needs to be worked on exists, returns `Just x`, else returns `Nothing`
switchWorkSameIdx :: Int -> WorkMap a -> (Maybe a, WorkMap a)
switchWorkSameIdx idx workMap
    | Just (workNeeded, workSat, mergeable) <- HM.lookup idx workMap
    , x S.:<| xs <- workNeeded =
        let workMap' = HM.insert idx (xs, workSat, mergeable) workMap -- Remove `x` from `workMap`
        in (Just x, workMap')
    | otherwise = (Nothing, workMap)

-- | Merges all mergeable objects at the current `idx`, and adds the merged objects to the new index returned by merge_func.
-- (In the runReducerMerge instance, merge_func would return the earlier index in the state's stack)
-- For all objects with implicit status WorkSaturated, resets them to status `WorkNeeded` by placing them in the appropriate Seq.
switchIdx :: WorkGraph a b -> (Bool, WorkGraph a b)
switchIdx wGraph@(WorkGraph { wMap = workMap, wPlan = workPlan, merge_func = mergeFunc , curr_idx = idx, context = ctxt }) =
    let (_, workSat, toMerge) = fromJust $ HM.lookup idx workMap -- should not be any objects with status WorkNeeded

        (workNeeded, merged, maybeNewIdx, ctxt') = mergeFunc workSat toMerge ctxt

        workPlan' = case workPlan of -- delete current index
            (_ S.:<| rest) -> rest
            S.Empty -> S.Empty
        workPlan'' = if (not $ S.null workNeeded) then workPlan' S.|> idx else workPlan'
        workPlan''' = maybe workPlan'' (\newIdx -> workPlan'' S.|> newIdx) maybeNewIdx

        (workNeededNew, workSatNew, mergeableNew) = maybe (S.empty, S.empty, S.empty) (\newIdx ->
            maybe (S.empty, S.empty, S.empty) id (HM.lookup newIdx workMap)) maybeNewIdx
        workNeededNew' = workNeededNew S.>< merged -- if merged is not null, it is guaranteed that maybeNewIdx is not Nothing
        workMap' = HM.insert idx (workNeeded, S.empty, S.empty) $ maybe workMap (\newIdx ->
            HM.insert newIdx (workNeededNew', workSatNew, mergeableNew) workMap) maybeNewIdx

    in case workPlan''' of -- Check if there is an index to switch to
        (i S.:<| _) -> (False, wGraph { wMap = workMap', wPlan = workPlan''', curr_idx = i, context = ctxt' })
        _ -> (True, wGraph { wMap = workMap', wPlan = workPlan''', context = ctxt'})

-- | Pick available object from first possible index in `workMap`. Called when status is `Split` and new index has been added to front of workPlan
switchIdxNoMerge :: WorkGraph a b -> (Maybe a, WorkGraph a b)
switchIdxNoMerge wGraph@(WorkGraph { wMap = workMap, wPlan = workPlan })
    | (idx S.:<| _) <- workPlan
    , Just (workNeeded, workSat, mergeable) <- HM.lookup idx workMap
    , (x S.:<| xs) <- workNeeded =
        let workMap' = HM.insert idx (xs, workSat, mergeable) workMap -- remove first state from toReduce
        in (Just x, wGraph { wMap = workMap' })
    | (_ S.:<| xs@(x S.:<| _)) <- workPlan = pickWork' (wGraph { wPlan = xs, curr_idx = x}) -- result of split has no reduceds,back to parent
    | otherwise = (Nothing, wGraph)

-- Prints string representation of work and increments a count when outputLog is called
data Logger a = Logger (a -> String) Int

outputLog :: Logger a -> a -> IO (Logger a)
outputLog (Logger logFn i) a = do
    print $ "Num: " ++ show i ++ (logFn a)
    return (Logger logFn (i + 1))
