module G2.Execution.WorkGraph ( WorkGraph(..)
                              , Status(..)
                              , WorkMap
                              , initGraph
                              , work) where

import qualified Data.Sequence as S
import qualified Data.Map as M

data Status = WorkNeeded | WorkSaturated | Split | Mergeable | Accept | Discard

-- (WorkNeeded, WorkSaturated, Mergeable)
type WorkMap a = M.Map Int (S.Seq a, S.Seq a, S.Seq a)
type WorkPlan = S.Seq Int

data WorkGraph a b = WorkGraph { wPlan :: WorkPlan
                               , wMap :: WorkMap a
                               , work_func :: a -> b -> IO ([a], b, Status)
                               , merge_func ::  WorkMap a -> b -> Int -> (S.Seq a, S.Seq a, Maybe Int, b)
                               , add_idx_func :: Int -> a -> a
                               , curr_idx :: Int
                               , max_idx :: Int
                               , context :: b
                               }

initGraph :: a
          -> b
          -> (a -> b -> IO ([a], b, Status))
          -> (WorkMap a -> b -> Int -> (S.Seq a, S.Seq a, Maybe Int, b))
          -> (Int -> a -> a)
          -> WorkGraph a b
initGraph fstWork ctxt workFunc mergeFunc addIdxFunc =
    let workMap = M.singleton 0 (S.singleton fstWork, S.empty, S.empty)
        workPlan = S.singleton 0
    in WorkGraph {
          wPlan = workPlan
        , wMap = workMap
        , work_func = workFunc
        , merge_func = mergeFunc
        , add_idx_func = addIdxFunc
        , curr_idx = 0
        , max_idx = 0
        , context = ctxt }

work :: WorkGraph a b -> IO ([a], b)
work wGraph = do
    let (a, wGraph') = pickWork WorkNeeded wGraph -- what about case where very first state is accepted/discarded
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
    , context = ctxt}) a accepted = do
    (as, ctxt', status) <- workFunc a ctxt
    let wGraph' = wGraph { context = ctxt' }
    let (accepted', wGraph'') = case status of
            Accept -> (as ++ accepted, wGraph')
            Discard -> (accepted, wGraph')
            Mergeable ->
                let workMap' = addMergeable workMap idx (head as)
                in (accepted, wGraph' { wMap = workMap' })
            WorkSaturated ->
                let workMap' = addSaturated workMap idx (head as)
                in (accepted, wGraph' { wMap = workMap' })
            Split ->
                let newIdx = maxIdx + 1
                    as' = map (addIdx newIdx) as -- implicit interface (e.g. a stack of indices)
                    workMap' = M.insert newIdx (S.fromList as', S.empty, S.empty) workMap
                    workPlan' = newIdx S.<| workPlan
                in (accepted, wGraph' { wMap = workMap', wPlan = workPlan', max_idx = newIdx, curr_idx = newIdx })
            WorkNeeded ->
                let workMap' = addWorkNeededMany workMap idx as
                in (accepted, wGraph' { wMap = workMap' })
    let (a', wGraph''') = pickWork status wGraph''
    case a' of
        Just a'' -> work' wGraph''' a'' accepted'
        Nothing -> return (accepted', context wGraph''')

-- Add state to appropriate Seq in the set of states for the specified index `idx`.
addMergeable :: WorkMap a -> Int -> a -> WorkMap a
addMergeable workMap idx a
    | Just (workNeeded, workSat, toMerge) <- M.lookup idx workMap =
        let toMerge' = toMerge S.|> a
        in M.insert idx (workNeeded, workSat, toMerge') workMap
    | otherwise = M.insert idx (S.empty, S.empty, S.singleton a) workMap

addSaturated :: WorkMap a -> Int -> a -> WorkMap a
addSaturated workMap idx a
    | Just (workNeeded, workSat, toMerge) <- M.lookup idx workMap =
        let workSat' = workSat S.|> a
        in M.insert idx (workNeeded, workSat', toMerge) workMap
    | otherwise = M.insert idx (S.empty, S.singleton a, S.empty) workMap

-- Add list of ExStates `toAdd` to Sequence of states to reduce, at the specified index `idx`
-- need to change name
addWorkNeededMany :: WorkMap a -> Int -> [a] -> WorkMap a
addWorkNeededMany workMap idx as =
    let idxAs = M.lookup idx workMap
    in case idxAs of
        Just (workNeeded, workSat, toMerge) -> M.insert idx (foldr (\s workNeeded' -> s S.<| workNeeded') workNeeded as,  workSat, toMerge) workMap
        Nothing -> M.insert idx (S.fromList as, S.empty, S.empty) workMap

pickWork  :: Status -> WorkGraph a b -> (Maybe a, WorkGraph a b)
pickWork status wGraph =
    case status of
        Accept -> pickWork' wGraph
        Discard -> pickWork' wGraph
        Mergeable -> pickWork' wGraph
        WorkSaturated ->  pickWork' wGraph
        Split -> switchIdxNoMerge wGraph
        WorkNeeded -> pickWork' wGraph

-- Search set of Work items in current index `idx` for next Work. If none available, merge all possible states in current idx,
-- and pick state in new idx to reduce.
pickWork' :: WorkGraph a b -> (Maybe a, WorkGraph a b)
pickWork' wGraph@(WorkGraph { wMap = workMap, curr_idx = idx }) =
    let (maybeW, workMap') = switchWorkSameIdx idx workMap
        wGraph' = wGraph { wMap = workMap' }
    in case maybeW of
        Just next -> (Just next, wGraph')
        Nothing ->
            let (halt, wGraph'') = switchIdx wGraph'
            in if halt then (Nothing, wGraph'') else pickWork' wGraph''

-- If a state s that can be reduced with same `idx` exists, returns Just s, else returns Nothing
switchWorkSameIdx :: Int -> WorkMap a -> (Maybe a, WorkMap a)
switchWorkSameIdx idx workMap
    | Just (workNeeded, workSat, toMerge) <- M.lookup idx workMap
    , x S.:<| xs <- workNeeded =
        let workMap' = M.insert idx (xs, workSat, toMerge) workMap
        in (Just x, workMap')
    | otherwise = (Nothing, workMap)

-- Merges all possible states at the current `idx`, and adds the merged states to the previous idx in their merge_stacks.
-- For all other states (i.e. those that have reached max depth), resets the unmerged case expr counts.
switchIdx :: WorkGraph a b -> (Bool, WorkGraph a b)
switchIdx wGraph@(WorkGraph { wMap = workMap, wPlan = workPlan, merge_func = mergeFunc , curr_idx = idx, context = ctxt }) =
    let (workNeeded, merged, maybeNewIdx, ctxt') = mergeFunc workMap ctxt idx

        workPlan' = case workPlan of
            (_ S.:<| rest) -> rest
            S.Empty -> S.Empty
        workPlan'' = if (not $ S.null workNeeded) then workPlan' S.|> idx else workPlan'
        workPlan''' = maybe workPlan'' (\newIdx -> workPlan'' S.|> newIdx) maybeNewIdx

        -- add new merged workMap to set at maybeNewIdx
        (oldToReduce, oldWorkSat, oldToMerge) = maybe (S.empty, S.empty, S.empty) (\newIdx ->
            maybe (S.empty, S.empty, S.empty) id (M.lookup newIdx workMap)) maybeNewIdx
        oldToReduce' = oldToReduce S.>< merged -- if merged is not null, it is guaranteed that maybeNewIdx is not Nothing
        workMap' = maybe workMap (\newIdx ->
            M.insert idx (workNeeded, S.empty, S.empty) $ M.insert newIdx (oldToReduce', oldWorkSat, oldToMerge) workMap) maybeNewIdx

    in case workPlan''' of
        (i S.:<| _) -> (False, wGraph { wMap = workMap', wPlan = workPlan''', curr_idx = i, context = ctxt' })
        _ -> (True, wGraph { wMap = workMap', wPlan = workPlan''', context = ctxt'})

-- Pick available state from first possible index in `evalSeq`
switchIdxNoMerge :: WorkGraph a b -> (Maybe a, WorkGraph a b)
switchIdxNoMerge wGraph@(WorkGraph { wMap = workMap, wPlan = workPlan })
    | (idx S.:<| _) <- workPlan
    , Just (workNeeded, workSat, toMerge) <- M.lookup idx workMap
    , (x S.:<| xs) <- workNeeded =
        let workMap' = M.insert idx (xs, workSat, toMerge) workMap -- remove first state from toReduce
        in (Just x, wGraph { wMap = workMap' })
    | (_ S.:<| xs@(x S.:<| _)) <- workPlan = pickWork' (wGraph { wPlan = xs, curr_idx = x}) -- result of split has no reduceds,back to parent
    | otherwise = (Nothing, wGraph)
