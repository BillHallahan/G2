module G2.Solver.AssumePCSolver ( AssumePCSolver (..)) where

import G2.Language.ArbValueGen
import G2.Language.Support
import G2.Language.Syntax
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import G2.Language.Ids  
import G2.Solver.Solver
import G2.Execution.StateMerging

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (null)

data AssumePCSolver a = AssumePCSolver ArbValueFunc a

instance Solver solver => Solver (AssumePCSolver solver) where
    check (AssumePCSolver _ sol) s pc = return . fst =<< checkRelAssume (Tr sol) s pc
    solve (AssumePCSolver avf sol) s b is pc =
        return . (\((r, m, _),_) -> (r, m)) =<< solveRelAssume avf (Tr sol) s b is pc
    close (AssumePCSolver _ s) = close s

instance TrSolver solver => TrSolver (AssumePCSolver solver) where
    checkTr (AssumePCSolver avf sol) s pc = do
        (r, sol') <- checkRelAssume sol s pc
        return (r, AssumePCSolver avf sol')
    solveTr (AssumePCSolver avf sol) s b is pc = do
        ((r, m, sol'),_) <- solveRelAssume avf sol s b is pc
        return (r, m, AssumePCSolver avf sol')
    closeTr (AssumePCSolver _ s) = closeTr s


checkRelAssume :: TrSolver a => a -> State t -> PathConds -> IO (Result, a)
checkRelAssume sol s pc = do
    res <- checkOrdinarySets sol s ordSets 
    case res of -- only if the sets without any AssumePCs in them are consistent do we check the remaining sets
        (SAT, sol') -> checkAssumePCSets sol' s assPCSets'
        r -> return r
    where
        relSets = PC.relatedSets (known_values s) pc -- All (AssumePCs i _ _) with same i will be grouped into same set
        (assPCSets, ordSets) = partition anyAssumePC relSets
        -- splitPCsId and relatedSets together split pc into sets s.t in each set, any top level AssumePCs have the same Id
        -- relatedSets alone not enough, because sometimes sets with AssumePCs with different Ids might might be grouped into the same set
        assPCSets' = concat $ map splitPCsId assPCSets

-- | Checks consistency of [PathConds] where each PathConds does not contain any AssumePCs
checkOrdinarySets :: TrSolver a => a -> State t -> [PathConds] -> IO (Result, a)
checkOrdinarySets sol _ [] = return (SAT, sol)
checkOrdinarySets sol s (p:ps) = do
        (c, sol') <- checkTr sol s p
        case c of
            SAT -> checkOrdinarySets sol' s ps
            _ -> return (c, sol')

-- | Checks consistency of [PathConds] where each PathConds contains path constraints of the form (AssumePC i _ _) for some Id i
-- e.g. [PathConds]!!0 could contain path constaints with Id 'x', while [PathConds]!!1 could contain path constraints with Id 'y'
checkAssumePCSets :: TrSolver a => a -> State t -> [PathConds] -> IO (Result, a)
checkAssumePCSets sol _ [] = return (SAT, sol)
checkAssumePCSets sol s (p:ps) = do
    -- split PathConds into sets based on Int in (AssumePC _ Int _), and check if at least one set is satisfiable
    (c, sol') <- checkAssumePCSets' sol s $ genPCsList s p
    case c of
        SAT -> checkAssumePCSets sol' s ps
        _ -> return (c, sol')

-- | Checks if at least one PathConds is satisfiable
checkAssumePCSets' :: TrSolver a => a -> State t -> [PathConds] -> IO (Result, a)
checkAssumePCSets' sol _ [] = return (UNSAT, sol)
checkAssumePCSets' sol s (p:ps) = do
    (res,sol') <- checkRelAssume sol s p
    case res of
        UNSAT -> checkAssumePCSets' sol' s ps
        _ -> return (res, sol')

-- Analogous functions to check*, but generates a Maybe Model too
solveRelAssume :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> [Id] -> PathConds -> IO ((Result, Maybe Model, a), [Id])
solveRelAssume avf sol s b is pc = do
    (res, is') <- solveOrdinarySets avf sol s b M.empty is ordSets
    case res of
        -- only check groups with any AssumePCs in them if the common PCs are consistent
        (SAT, Just m', sol') -> solveAssumePCSets avf sol' s b m' (is') assPCSets'
        r -> return (r, is')
    where
        relSets = PC.relatedSets (known_values s) pc -- All (AssumePCs i _ _) with same i will be grouped into same set
        (assPCSets, ordSets) = partition anyAssumePC relSets
        assPCSets' = concat $ map splitPCsId assPCSets -- ensure that each set consists of top level AssumePCs with same Id

solveOrdinarySets :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> Model -> [Id] -> [PathConds] -> IO ((Result, Maybe Model, a), [Id])
solveOrdinarySets _ sol _ _ m is [] = return ((SAT, Just m, sol), is)
solveOrdinarySets avf sol s b m is (p:ps) = do
    let is' = concat $ PC.map (PC.varIdsInPC (known_values s)) p
    let is'' = ids p
    rm <- solveTr sol s b is' p
    case rm of
        (SAT, Just m', sol') -> solveOrdinarySets avf sol' s b (M.union m m') (is ++ is'') ps
        rm' -> return (rm', is'')

solveAssumePCSets :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> Model -> [Id] -> [PathConds] -> IO ((Result, Maybe Model, a), [Id])
solveAssumePCSets avf sol s b m is [] =
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
    in return ((SAT, Just m', sol), is)
solveAssumePCSets avf sol s b m is (p:ps) = do
    (rm, is') <- solveAssumePCSets' avf sol s b m $ genPCsList s p
    case rm of
        (SAT, Just m', sol') -> solveAssumePCSets avf sol' s b (M.union m m') (is ++ is') ps
        _ -> return (rm, is)

solveAssumePCSets' :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> Model -> [PathConds] -> IO ((Result, Maybe Model, a), [Id])
solveAssumePCSets' _ sol _ _ _ [] = return ((UNSAT, Nothing, sol), [])
solveAssumePCSets' avf sol s b m (p:ps) = do
    (rm, is) <- solveRelAssume avf sol s b [] p
    case rm of
        (UNSAT, _, sol') -> solveAssumePCSets' avf sol' s b m ps
        (SAT, Just m', sol') -> return ((SAT, Just (M.union m' m), sol'), is)
        _ -> return (rm, is)


-- Helper Functions

-- | Split into sets based on Id in (AssumePC Id _ _), for PathConds not of the form Assume PC, add to all sets
splitPCsId ::PathConds -> [PathConds]
splitPCsId pc =
    let
        assumePCs = PC.filter isAssumePC pc
        uniqueAssumes = nub $ PC.map getAssumeIds assumePCs -- get list of unique Ids from the AssumePCs
        -- filters unrelated pcs and adds the (Id, Int) pair from an AssumePC as an extCond, to constrain checking/solving for the id
        f = (\i -> (filterById pc i))
    in
    fmap f uniqueAssumes

-- | Split into sets based on Int in (AssumeExpr _ Int _), and extract PathCond in any top level AssumePCs
genPCsList :: State t -> PathConds -> [PathConds]
genPCsList s pc =
    let
        assumePCs = PC.filter isAssumePC pc
        uniqueAssumes = nub $ PC.map getAssumeIdInt assumePCs -- get list of unique (Id, Int) pairs from the AssumePCs
        createExtCond = (\(i, val) -> (ExtCond (createEqExpr (known_values s) i (toInteger val)) True))
        -- filters unrelated pcs and adds the (Id, Int) pair from an AssumePC as an extCond, to constrain checking/solving for the id
        f = (\(i, val) -> (PC.insert (known_values s) (createExtCond (i,val)) (filterByIdInt pc (i,val))))
    in
    extractPCs (known_values s) $ fmap f uniqueAssumes

-- | Filters all AssumePCs with a different assumed (Id, Int) value
filterByIdInt :: PathConds -> (Id, Int) -> PathConds
filterByIdInt pc e = PC.filter (otherAssumePCs e) pc

otherAssumePCs :: (Id, Int) -> PathCond -> Bool
otherAssumePCs i (AssumePC i' num' _) = i == (i', num')
otherAssumePCs _ _ = True

-- | Filters all AssumePCs with a different assumed Id
filterById :: PathConds -> Id -> PathConds
filterById pc i = PC.filter (otherIds i) pc

otherIds :: Id -> PathCond -> Bool
otherIds i (AssumePC i' _  _) = i == i'
otherIds _ _ = True

-- | For each PathCond in [PathConds], extracts the inner pc if PathCond is of form (AssumePC _ _ pc)
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

getAssumeIdInt :: PathCond -> (Id, Int)
getAssumeIdInt (AssumePC i num _) = (i, num)
getAssumeIdInt _ = error "Pathcond is not of the form (AssumePC _ _)."

getAssumeIds :: PathCond -> Id
getAssumeIds (AssumePC i _ _) = i
getAssumeIds _ = error "Pathcond is not of the form (AssumePC _ _)."

