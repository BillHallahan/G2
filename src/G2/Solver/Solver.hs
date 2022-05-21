{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module G2.Solver.Solver ( Solver (..)
                        , TrSolver (..)
                        , Tr (..)
                        , SomeSolver (..)
                        , SomeTrSolver (..)
                        , Result (..)
                        , GroupRelated (..)
                        , groupRelatedFinite
                        , groupRelatedInfinite
                        , CombineSolvers (..)
                        , UndefinedHigherOrder (..)
                        , UnknownSolver (..)) where

import G2.Language
import qualified G2.Language.PathConds as PC
import Data.List
import qualified Data.HashMap.Lazy as HM

-- | The result of a Solver query
data Result m u um = SAT m
                   | UNSAT u
                   | Unknown String um
                   deriving (Show, Eq)

-- | Defines an interface to interact with Solvers
class Solver solver where
    -- | Checks if the given `PathConds` are satisfiable.
    check :: forall t . solver -> State t -> PathConds -> IO (Result () () ())
    
    -- | Checks if the given `PathConds` are satisfiable, and, if yes, gives a `Model`
    -- The model must contain, at a minimum, a value for each passed `Id`
    solve :: forall t . solver -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () ())

    -- | Cleans up when the solver is no longer needed.  Default implementation
    -- does nothing
    close :: solver -> IO ()
    close _ = return ()

-- | Defines an interface to interact with Tracking Solvers-
-- solvers that can track some sort of state.
-- Every solver is also a tracking solver, so this is the more general type.
-- Typically, all functions should be written using TrSolver, rather than Solver.
class TrSolver solver where
    -- | Checks if the given `PathConds` are satisfiable.
    -- Allows modifying the solver, to track some state.
    checkTr :: forall t . solver -> State t -> PathConds -> IO (Result () () (), solver)
    
    -- | Checks if the given `PathConds` are satisfiable, and, if yes, gives a `Model`
    -- The model must contain, at a minimum, a value for each passed `Id`
    -- Allows modifying the solver, to track some state.
    solveTr :: forall t . solver -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () (), solver)

    -- | Cleans up when the solver is no longer needed.  Default implementation
    -- does nothing
    closeTr :: solver -> IO ()
    closeTr _ = return ()

-- | A wrapper to turn something that is a Solver into a TrSolver
newtype Tr solver = Tr { unTr :: solver }

instance Solver solver => TrSolver (Tr solver) where
    checkTr (Tr sol) s pc = return . (, Tr sol) =<< check sol s pc
    solveTr (Tr sol) s b is pc = return . (\r -> (r, Tr sol)) =<< solve sol s b is pc
    closeTr = close . unTr

data SomeSolver where
    SomeSolver :: forall solver
                . Solver solver => solver -> SomeSolver

data SomeTrSolver where
    SomeTrSolver :: forall solver
                  . TrSolver solver => solver -> SomeTrSolver

-- | Splits path constraints before sending them to the rest of the solvers
data GroupRelated a = GroupRelated ArbValueFunc a

groupRelatedFinite :: a -> GroupRelated a
groupRelatedFinite = GroupRelated arbValue

groupRelatedInfinite :: a -> GroupRelated a
groupRelatedInfinite = GroupRelated arbValueInfinite

checkRelated :: TrSolver a => a -> State t -> PathConds -> IO (Result () () (), a)
checkRelated solver s pc =
    checkRelated' solver s $ PC.relatedSets pc

checkRelated' :: TrSolver a => a -> State t -> [PathConds] -> IO (Result () () (), a)
checkRelated' sol _ [] = return (SAT (), sol)
checkRelated' sol s (p:ps) = do
    (c, sol') <- checkTr sol s p
    case c of
        SAT _ -> checkRelated' sol' s ps
        r -> return (r, sol')

solveRelated :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () (), a)
solveRelated avf sol s b is pc = do
    solveRelated' avf sol s b HM.empty is $ PC.relatedSets pc

solveRelated' :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> Model -> [Id] -> [PathConds] -> IO (Result Model () (), a)
solveRelated' avf sol s b m is [] =
    let 
        is' = filter (\i -> not $ idName i `HM.member` m) is

        (_, nv) = mapAccumL
            (\av_ (Id n t) ->
                let 
                    (av_', v) = avf t (type_env s) av_
                    in
                    (v, (n, av_'))
            ) (arb_value_gen b) is'

        m' = foldr (\(n, v) -> HM.insert n v) m nv
    in
    return (SAT m', sol)
solveRelated' avf sol s b m is (p:ps) = do
    let is' = concat $ PC.map' PC.varIdsInPC p
    let is'' = ids p
    rm <- solveTr sol s b is' p
    case rm of
        (SAT m', sol') -> solveRelated' avf sol' s b (HM.union m m') (is ++ is'') ps
        rm' -> return rm'

instance Solver solver => Solver (GroupRelated solver) where
    check (GroupRelated _ sol) s pc = return . fst =<< checkRelated (Tr sol) s pc
    solve (GroupRelated avf sol) s b is pc =
        return . (\(r, _) -> r) =<< solveRelated avf (Tr sol) s b is pc
    close (GroupRelated _ s) = close s

instance TrSolver solver => TrSolver (GroupRelated solver) where
    checkTr (GroupRelated avf sol) s pc = do
        (r, sol') <- checkRelated sol s pc
        return (r, GroupRelated avf sol')
    solveTr (GroupRelated avf sol) s b is pc = do
        (r, sol') <- solveRelated avf sol s b is pc
        return (r, GroupRelated avf sol')
    closeTr (GroupRelated _ s) = closeTr s

-- | Allows solvers to be combined, to exploit different solvers abilities
-- to solve different kinds of constraints
data CombineSolvers a b = a :<? b -- ^ a :<? b - Try solver b.  If it returns Unknown, try solver a
                        | a :?> b -- ^ a :>? b - Try solver a.  If it returns Unknown, try solver b

checkWithEither :: (TrSolver a, TrSolver b) => a -> b -> State t -> PathConds -> IO (Result () () (), CombineSolvers a b)
checkWithEither a b s pc = do
    (ra, a') <- checkTr a s pc 
    case ra of
        SAT _ -> return (ra, a' :?> b)
        UNSAT _ -> return (ra, a' :?> b)
        Unknown ua _ -> do
            (rb, b') <- checkTr b s pc
            case rb of
                Unknown ub _ -> return $ (Unknown (ua ++ ",\n" ++ ub) (), a' :?> b')
                rb' -> return (rb', a' :?> b')

solveWithEither :: (TrSolver a, TrSolver b) => a -> b -> State t -> Bindings -> [Id] -> PathConds -> IO (Result Model () (), CombineSolvers a b)
solveWithEither a b s binds is pc = do
    ra <- solveTr a s binds is pc 
    case ra of
        (SAT m, a') -> return (SAT m, a' :?> b)
        (UNSAT u, a') -> return (UNSAT u, a' :?> b)
        (Unknown ua _, a') -> do
            rb <- solveTr b s binds is pc
            case rb of
                (Unknown ub (), b') -> return $ (Unknown (ua ++ ",\n" ++ ub) (), a' :?> b')
                (r, b') -> return (r, a' :?> b')

-- | Fills in unused higher order functions with undefined
data UndefinedHigherOrder = UndefinedHigherOrder

instance Solver UndefinedHigherOrder where
    check _ _ pc =
        let
            f = concatMap PC.varIdsInPC  $ PC.toList pc
        in
        case f of
            [Id _ (TyFun _ _)] -> return $ SAT ()
            _ -> return $ Unknown "UndefinedHigherOrder" ()

    solve _ _ _ [i@(Id _ (TyFun _ _))] _ =
        return $ SAT (HM.singleton (idName i) (Prim Undefined TyBottom))
    solve _ _ _ _ _ = return (Unknown "UndefinedHigherOrder" ())

instance (Solver a, Solver b) => Solver (CombineSolvers a b) where
    check (a :<? b) s pc = return . fst =<< checkWithEither (Tr b) (Tr a) s pc
    check (a :?> b) s pc = return . fst =<< checkWithEither (Tr a) (Tr b) s pc

    solve (a :<? b) s binds is pc =
        return . (\(r, _) -> r) =<< solveWithEither (Tr b) (Tr a) s binds is pc
    solve (a :?> b) s binds is pc =
        return . (\(r, _) -> r) =<< solveWithEither (Tr a) (Tr b) s binds is pc

    close (a :<? b) = do
        close a
        close b
    close (a :?> b) = do
        close a
        close b

instance (TrSolver a, TrSolver b) => TrSolver (CombineSolvers a b) where
    checkTr (a :<? b) s pc = do
        (r, sol') <- checkWithEither b a s pc
        case sol' of
            b' :?> a' -> return (r, a' :<? b')
            b' :<? a' -> return (r, a' :?> b')
    checkTr (a :?> b) s pc = checkWithEither a b s pc

    solveTr (a :<? b) s binds is pc = do
        (r, sol') <- solveWithEither b a s binds is pc
        case sol' of
            b' :?> a' -> return (r, a' :<? b')
            b' :<? a' -> return (r, a' :?> b')
    solveTr (a :?> b) s binds is pc = solveWithEither a b s binds is pc

    closeTr (a :<? b) = do
        closeTr a
        closeTr b
    closeTr (a :?> b) = do
        closeTr a
        closeTr b

instance (ASTContainer m e, ASTContainer u e) => ASTContainer (Result m u um) e where
    containedASTs (SAT m) = containedASTs m
    containedASTs (UNSAT u) = containedASTs u
    containedASTs (Unknown _ _) = []

    modifyContainedASTs f (SAT m) = SAT (modifyContainedASTs f m)
    modifyContainedASTs f (UNSAT u) = UNSAT (modifyContainedASTs f u)
    modifyContainedASTs _ u@(Unknown _ _) = u

-- A solver that returns unknown on all but the most trivial (empty) PCs
data UnknownSolver = UnknownSolver

instance Solver UnknownSolver where
    check _ _ pc
        | PC.null pc = return (SAT ())
        | otherwise = return (Unknown "unknown" ())
    solve _ _ _ _ pc
        | PC.null pc = return (SAT HM.empty)
        | otherwise = return (Unknown "unknown" ())
