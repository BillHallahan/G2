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
import qualified Data.HashMap.Lazy as HM
import Data.Maybe

-- | Converts constraints about ADTs to numerical constraints before sending them to other solvers
data ADTNumericalSolver solver = ADTNumericalSolver ArbValueFunc solver

adtNumericalSolFinite :: solver -> ADTNumericalSolver solver
adtNumericalSolFinite = ADTNumericalSolver arbValue

adtNumericalSolInfinite :: solver -> ADTNumericalSolver solver
adtNumericalSolInfinite = ADTNumericalSolver arbValueInfinite

instance Solver solver => Solver (ADTNumericalSolver solver) where
    check (ADTNumericalSolver _ sol) s pc = return . fst =<< checkConsistency (Tr sol) s pc
    solve (ADTNumericalSolver avf sol) s b is pc =
        return . (\(r, _) -> r) =<< solve' avf (Tr sol) s b is pc
    close (ADTNumericalSolver _ s) = close s

instance TrSolver solver => TrSolver (ADTNumericalSolver solver) where
    checkTr (ADTNumericalSolver avf sol) s pc = do
        (r, sol') <- checkConsistency sol s pc
        return (r, ADTNumericalSolver avf sol')
    solveTr (ADTNumericalSolver avf sol) s b is pc = do
        (r, sol') <- solve' avf sol s b is pc
        return (r, ADTNumericalSolver avf sol')
    closeTr (ADTNumericalSolver _ s) = closeTr s

checkConsistency :: TrSolver solver => solver -> State t -> PathConds -> IO (Result () (), solver)
checkConsistency solver s@(State {known_values = kv, expr_env = eenv}) pc
    | PC.null pc = return (SAT (), solver)
    | otherwise = do
        checkTr solver s pc

solve' :: TrSolver solver => ArbValueFunc -> solver -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model (), solver)
solve' avf sol s@(State {known_values = kv, type_env = tenv, expr_env = eenv}) b is pc = do
    solveTr sol s b is pc