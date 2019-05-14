module G2.Solver.AssumePCSolver ( AssumePCSolver (..)) where

import G2.Language.ArbValueGen
import G2.Language.Support
import G2.Language.Syntax
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import G2.Language.Ids  
import G2.Solver.Solver

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (null)


data AssumePCSolver a = AssumePCSolver a

instance Solver solver => Solver (AssumePCSolver solver) where
    check (AssumePCSolver sol) s pc = return . fst =<< checkRelAssume (Tr sol) s pc
    solve (AssumePCSolver sol) s b is pc =
        return . (\(r, m, _) -> (r, m)) =<< solveRelAssume (Tr sol) s b is pc
    close (AssumePCSolver s) = close s

instance TrSolver solver => TrSolver (AssumePCSolver solver) where
    checkTr (AssumePCSolver sol) s pc = do
        (r, sol') <- checkRelAssume sol s pc
        return (r, AssumePCSolver sol')
    solveTr (AssumePCSolver sol) s b is pc = do
        (r, m, sol') <- solveRelAssume sol s b is pc
        return (r, m, AssumePCSolver sol')
    closeTr (AssumePCSolver s) = closeTr s

-- | Separates PCs into related sets, and extracts pc from any (AssumePC _  _ pc) in each set, before sending them to the next solver
checkRelAssume :: TrSolver a => a -> State t -> PathConds -> IO (Result, a)
checkRelAssume solver s pc = checkRelAssume' solver s $ genPCsList s pc

checkRelAssume' :: TrSolver a => a -> State t -> [PathConds] -> IO (Result, a)
checkRelAssume' sol _ [] = return (SAT, sol)
checkRelAssume' sol s (p:ps) = do
    (c, sol') <- checkTr sol s p
    case c of
        SAT -> checkRelAssume' sol' s ps
        r -> return (r, sol')

solveRelAssume :: TrSolver a => a -> State t -> Bindings -> [Id] -> PathConds -> IO (Result, Maybe Model, a)
solveRelAssume sol s b is pc = solveRelAssume' sol s b M.empty is $ genPCsList s pc

solveRelAssume' :: TrSolver a => a -> State t -> Bindings -> Model -> [Id] -> [PathConds] -> IO (Result, Maybe Model, a)
solveRelAssume' sol s b m is [] =
    let 
        is' = filter (\i -> idName i `M.notMember` m) is
        nv = map (\(Id n t) -> (n, fst $ arbValue t (type_env s) (arb_value_gen b))) is'
        m' = foldr (\(n, v) -> M.insert n v) m nv
    in
    return (SAT, Just m', sol)
solveRelAssume' sol s b m is (p:ps) = do
    let is' = concat $ PC.map (PC.varIdsInPC (known_values s)) p
    let is'' = ids p
    rm <- solveTr sol s b is' p
    case rm of
        (SAT, Just m', sol') -> solveRelAssume' sol' s b (M.union m m') (is ++ is'') ps
        rm' -> return rm'

-- Helper Functions

-- | Given a PathConds, recursively splits the constituent PathCond-s into related sets, each time extracting the pc out of any AssumePCs
-- Union of output should be the input PathConds
genPCsList :: State t -> PathConds -> [PathConds]
genPCsList s pc = concat (fmap (\relSet ->
                                    if anyAssumePC relSet
                                        then genPCsList' s relSet
                                        else [relSet]) relSets)
                 where
                    relSets = PC.relatedSets (known_values s) pc -- All (AssumePCs i _ _) with same i will be grouped into same set

genPCsList' :: State t -> PathConds -> [PathConds]
genPCsList' s pc =
    let
        assumePCs = PC.filter isAssumePC pc
        uniqueAssumes = nub $ PC.map getAssumes assumePCs -- get list of unique (Id, Int) pairs from the AssumePCs
    in
    concat $ fmap (genPCsList s) $ extractPCs (known_values s) $ fmap (filterUnrelatedPCs pc) uniqueAssumes

-- Filters all AssumePCs with a different assumed (Id, Int) value
filterUnrelatedPCs :: PathConds -> (Id, Int) -> PathConds
filterUnrelatedPCs pc e = PC.filter (otherAssumePCs e) pc

otherAssumePCs :: (Id, Int) -> PathCond -> Bool
otherAssumePCs i (AssumePC i' num' _) = i == (i', num')
otherAssumePCs _ _ = True

-- | For each PathCond in [PathConds], extracts the inner pc if PathCond is of form (AssumePC e pc)
extractPCs :: KV.KnownValues -> [PathConds] -> [PathConds]
extractPCs kv (pc:pcs) = PC.fromList kv (PC.map extractPC pc) : extractPCs kv pcs
extractPCs _ [] = []

extractPC :: PathCond -> PathCond
extractPC (AssumePC _ _ pc) = pc
extractPC pc = pc

isAssumePC :: PathCond -> Bool
isAssumePC (AssumePC _ _ _) = True
isAssumePC _ = False

anyAssumePC :: PathConds -> Bool
anyAssumePC pc = any isAssumePC $ PC.toList pc

getAssumes :: PathCond -> (Id, Int)
getAssumes (AssumePC i num _) = (i, num)
getAssumes _ = error "Pathcond is not of the form (AssumePC _ _)."


