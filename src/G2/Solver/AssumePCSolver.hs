module G2.Solver.AssumePCSolver ( AssumePCSolver (..)
                                , Cache(..) ) where

import G2.Language
import qualified G2.Language.PathConds as PC
import G2.Solver.Solver

import Data.List
import qualified Data.Map as M
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import Prelude hiding (null)

data Cache = Cache (HM.HashMap PathConds Result)

addToCache :: Cache -> PathConds -> Result -> Cache
addToCache (Cache hm) pc res = Cache $ HM.insert pc res hm

checkCache :: Cache -> PathConds -> Maybe Result
checkCache (Cache hm) pc = HM.lookup pc hm

data AssumePCSolver a = AssumePCSolver ArbValueFunc Cache a

instance Solver solver => TrSolver (AssumePCSolver solver) where
    checkTr (AssumePCSolver avf cache sol) s pc = do
        (r, cache', sol') <- checkTr' cache (Tr sol) s pc
        return (r, AssumePCSolver avf cache' (unTr sol'))
    solveTr (AssumePCSolver avf cache sol) s b is pc = do
        (r, m, sol') <- solveRelated avf (Tr sol) s b is pc
        return (r, m, AssumePCSolver avf cache (unTr sol'))
    closeTr (AssumePCSolver _ _ s) = close s

checkTr' :: TrSolver a => Cache -> a -> State t -> PathConds -> IO (Result, Cache, a)
checkTr' cache sol s pc = do
    let sets = PC.relatedSets (known_values s) pc -- All (AssumePCs i _ _) with same i will be grouped into same set
    (res, cache', sol') <- checkRelSets cache sol s sets
    let cache'' = addToCache cache' pc res
    return (res, cache'', sol')

-- Check each related set in turn for satisfiability. If any set results in UNSAT, terminate
checkRelSets :: TrSolver a => Cache -> a -> State t -> [PathConds] -> IO (Result, Cache, a)
checkRelSets cache sol s (pc:pcs) = do
    (res, cache', sol') <- checkRelSet cache sol s pc
    case res of
        SAT -> checkRelSets cache' sol' s pcs
        _ -> return (res, cache', sol')
checkRelSets cache sol _ [] = return (SAT, cache, sol)

checkRelSet :: TrSolver a => Cache -> a -> State t -> PathConds -> IO (Result, Cache, a)
checkRelSet cache sol s pc = do
    case checkCache cache pc of
        (Just res) -> return (res, cache, sol)
        _ -> if (not $ PC.existsAssumePC pc)
            then do
                (res, sol') <- checkTr sol s pc
                let cache' = addToCache cache pc res
                return (res, cache', sol')
            else do
                let pcSetsByInt = genPCSetsByInt s pc -- list of sets of PathCond-s grouped by Int in the AssumePC they appear in
                    nonAssumePCs = PC.genNonAssumePCs pc
                (res, cache', sol') <- checkSetsByInt cache sol s nonAssumePCs pcSetsByInt
                let cache'' = addToCache cache' pc res
                return (res, cache'', sol')

-- splits all AssumePCs in `pc` by Int in `AssumePC Id Int pc`, where Id == `i`, and lifts the pc out of the AssumePC
genPCSetsByInt :: State t -> PathConds -> [PathConds]
genPCSetsByInt (State { known_values = kv }) pc =
    -- get list of unique Ints from the AssumePCs, assume all top level AssumePCs have same Id
    let uniqueAssumes = nub $ filter (\a -> a >= 0) $ PC.map' PC.getAssumeInt pc
    -- seems terribly inefficient, to redesign
    in map (\i ->
        let hashedPCs = PC.filterByInt (PC.toHashedList pc) i
            assumePCId = PC.getAssumeId $ PC.unhashedPC (head hashedPCs)
            hashedPCs' = map PC.removeAssumes hashedPCs
            newPC = PC.hashedPC $ ExtCond (mkEqIntExpr kv (Var assumePCId) i) True
        in PC.fromHashedList (newPC:hashedPCs')) uniqueAssumes

checkSetsByInt :: TrSolver a => Cache -> a -> State t -> [PC.HashedPathCond] -> [PathConds] -> IO (Result, Cache, a)
checkSetsByInt cache sol s nonAssumePCs (pcSetByInt:pcs) = do
    (res, cache', sol') <- checkSetByInt cache sol s nonAssumePCs pcSetByInt
    case res of
        SAT -> return (res, cache', sol')
        _ -> checkSetsByInt cache' sol' s nonAssumePCs pcs
checkSetsByInt cache sol _ _ [] = return (UNSAT, cache, sol)

checkSetByInt :: TrSolver a => Cache -> a -> State t -> [PC.HashedPathCond] -> PathConds -> IO (Result, Cache, a)
checkSetByInt cache sol s nonAssumePCs pcSetByInt = do
    case checkCache cache pcSetByInt of
        (Just res) -> case res of
            UNSAT -> return (res, cache, sol)
            Unknown _ -> return (res, cache, sol)
            _ -> do
                let augmentedSet = foldl (\pcSet pc -> PC.insertHashed pc pcSet) pcSetByInt nonAssumePCs
                checkTr' cache sol s augmentedSet
        Nothing -> do 
            let augmentedSet = foldl (\pcSet pc -> PC.insertHashed pc pcSet) pcSetByInt nonAssumePCs
            checkTr' cache sol s augmentedSet


{-
checkTr (AssumePCSolver avf cache) s pc =
    sets = groupRelated pc
    res = unsat
    for each set in sets:
        if set in cache:
            res = cache[set]
        else if !containsAssumePC:
            res = solve(set)
            add (set,res) to cache
        else:
            res2 = unsat
            for each value i of N: -- where 'N' is the id name in (AssumePC id int pc)
                if set[N_i] in cache: -- set of pathconds that contain N_i
                    res2 = cache[set[N_i]]
                    if res2 == unsat:
                        continue
                smallSet = set[N_i] + set[null]
                res2, cache = checkTr cache s smallset
                if res2 == sat:
                    break
            res = res2
            add (set,res) to cache
        if res == unsat:
            break
    add (pc, res) to cache
    return (cache, res)
-}

-- Identical to GroupRelated solver --
solveRelated :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> [Id] -> PathConds -> IO (Result, Maybe Model, a)
solveRelated avf sol s b is pc = do
    solveRelated' avf sol s b M.empty is $ PC.relatedSets (known_values s) pc

solveRelated' :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> Model -> [Id] -> [PathConds] -> IO (Result, Maybe Model, a)
solveRelated' avf sol s b m is [] =
    let
        is' = filter (\i -> idName i `M.notMember` m) is

        (_, nv) = mapAccumL
            (\av_ (Id n t) ->
                let
                    (av_', v) = avf t (type_env s) av_
                    in
                    (v, (n, av_'))
            ) (arb_value_gen b) is'

        m' = foldr (\(n, v) -> M.insert n v) m nv
    in
    return (SAT, Just m', sol)
solveRelated' avf sol s b m is (p:ps) = do
    let is' = concat $ PC.map' PC.varIdsInPC p
    let is'' = ids p
    rm <- solveTr sol s b is' p
    case rm of
        (SAT, Just m', sol') -> solveRelated' avf sol' s b (M.union m m') (is ++ is'') ps
        rm' -> return rm'

