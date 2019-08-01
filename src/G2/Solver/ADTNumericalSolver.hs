{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.ADTNumericalSolver ( ADTNumericalSolver (..)
                                    , adtNumericalSolFinite
                                    , adtNumericalSolInfinite) where

import G2.Language.ArbValueGen
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Support
import G2.Language.Syntax
import qualified G2.Language.PathConds as PC
import G2.Language.Typing
import G2.Solver.Solver

import Data.List
import qualified Data.Map as M
import Data.Maybe

-- | Converts constraints about ADTs to numerical constraints before sending them to other solvers
data ADTNumericalSolver a = ADTNumericalSolver ArbValueFunc a

adtNumericalSolFinite :: a -> ADTNumericalSolver a
adtNumericalSolFinite = ADTNumericalSolver arbValue

adtNumericalSolInfinite :: a -> ADTNumericalSolver a
adtNumericalSolInfinite = ADTNumericalSolver arbValueInfinite

instance Solver solver => Solver (ADTNumericalSolver solver) where
    check (ADTNumericalSolver _ sol) s pc = return . fst =<< checkConsistency (Tr sol) s pc
    solve (ADTNumericalSolver avf sol) s b is pc =
        return . (\(r, m, _) -> (r, m)) =<< solve' avf (Tr sol) s b is pc
    close (ADTNumericalSolver _ s) = close s

instance TrSolver solver => TrSolver (ADTNumericalSolver solver) where
    checkTr (ADTNumericalSolver avf sol) s pc = do
        (r, sol') <- checkConsistency sol s pc
        return (r, ADTNumericalSolver avf sol')
    solveTr (ADTNumericalSolver avf sol) s b is pc = do
        (r, m, sol') <- solve' avf sol s b is pc
        return (r, m, ADTNumericalSolver avf sol')
    closeTr (ADTNumericalSolver _ s) = closeTr s

checkConsistency :: TrSolver a => a -> State t -> PathConds -> IO (Result, a)
checkConsistency solver s@(State {known_values = kv, simplified = smplfd, adt_int_maps = adtIntMaps, expr_env = eenv}) pc
    | PC.null pc = return (SAT, solver)
    | otherwise = do
        let ns = PC.pcNames pc
            eenvPCs = mapMaybe (addEEnvVals kv eenv smplfd adtIntMaps) ns
            pc' = foldr PC.insert pc $ eenvPCs
        checkTr solver s pc'

solve' :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> [Id] -> PathConds -> IO (Result, Maybe Model, a)
solve' avf sol s@(State {known_values = kv, simplified = smplfd, adt_int_maps = adtIntMaps, type_env = tenv, expr_env = eenv}) b is pc = do
    -- Split into Ids that need to be solved further by solvers, and Ids representing ADTs with no related PathConds
    let (rest, pcIds) = partition (f smplfd) is
        pcIdsPrim = map (\i@(Id n t) -> if (isADT t) then (Id n TyLitInt) else i) pcIds
        -- Get constraints from ExprEnv
        ns = PC.pcNames pc
        eenvPCs = mapMaybe (addEEnvVals kv eenv smplfd adtIntMaps) ns
        pc' = foldr PC.insert pc $ eenvPCs
    rm <- solveTr sol s b pcIdsPrim pc'
    case rm of
        (SAT, Just m, sol') -> do
            let (_, restM) = mapAccumL (genArbValue avf tenv eenv) b rest
            return (SAT, Just $ M.union (M.fromList restM) m, sol')
        _ -> return rm

-- If `n` is a member of smplfd, it means a PathCond containing `n` must have been added to PathConds earlier
f :: M.Map Name (Type, Type) -> Id -> Bool
f smplfd (Id n t) = ((not $ M.member n smplfd) && (isADT $ t))

-- Generate arbitrary value or lookup Name in ExprEnv
genArbValue :: ArbValueFunc -> TypeEnv -> ExprEnv -> Bindings -> Id -> (Bindings, (Name, Expr))
genArbValue avf tenv eenv b (Id n t)
    | not $ E.isSymbolic n eenv
    , Just e <- E.lookup n eenv = (b, (n, e))
    | TyCon tn k <- tyAppCenter t
    , ts <- tyAppArgs t =
        let
            (bse, av) = avf (mkTyApp (TyCon tn k:ts)) tenv (arb_value_gen b)
        in (b {arb_value_gen = av}, (n, bse))
    | otherwise = error $ "Unsolved Name of type: " ++ (show t)

-- Add any constraints from the ExprEnv
addEEnvVals :: KnownValues -> ExprEnv -> M.Map Name (Type, Type) -> ADTIntMaps -> Name -> Maybe PathCond
addEEnvVals kv eenv smplfd adtIntMaps n =
    let (_, newTyp) = fromJust $ M.lookup n smplfd
    in case E.lookup n eenv of
        Just e
            | Data (DataCon dcN _):_ <- unApp e ->
                let dcNumMap = fromJust $ M.lookup newTyp adtIntMaps
                    num = fromJust $ lookupInt dcN dcNumMap
                in Just $ ExtCond (mkEqIntExpr kv (Var (Id n TyLitInt)) (toInteger num)) True
        _ -> Nothing
