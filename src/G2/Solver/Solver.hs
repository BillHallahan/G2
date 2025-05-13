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
                        , UnknownSolver (..)
                        , EqualitySolver (..)
                        
                        , TimeSolver
                        , timeSolver
                        , timeSomeSolver
                        , CallsSolver
                        , callsSolver
                        , callsSomeSolver) where

import G2.Language
import qualified G2.Language.PathConds as PC
import Data.Graph
import Data.List
import qualified Data.HashMap.Lazy as HM
import Data.IORef
import System.Clock

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
                    (av_', v) = avf t (type_env s) (tyvar_env s) av_
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

-- | A solver that handles checking of certain equalities between variables and expressions.
-- In particular, if we have a set of path constraints of the form:
--    @ x_1 `op` e_1
--      x_2 `op` e_2
--      ..
--      x_n `op` e_n @
-- (For op one of ==, /=, >, >=, <, <=)
-- where x_i does not appear in e_j for any j <= i, then this path constraint is guaranteed to be satisfiable.
-- For i from e_1 to e_n, we can instantiate the variables in e_i, then solve e_i and assign an appropriate
-- value to x_i.
data EqualitySolver = EqualitySolver

instance Solver EqualitySolver where
    check _ _ pcs | Just m_v_vs <- sequence . map isolatedFormula $ PC.toList pcs
                  -- Check that the left hand side of all operators is unqiue, i.e. all x_i differ from each other
                  , uniq $ map fst m_v_vs
                  -- Check that there are no loops where x_i ... x_j appear on the RHS of each others equations
                  , not (cycleExists m_v_vs) = return $ SAT ()
                  | otherwise = return $ Unknown "Equality Solver: unsupported constraint" ()
    solve _ _ _ _ _ = return $ Unknown "Equality Solver does not support solving" ()
    close _ = return ()

isolatedFormula :: PathCond -> Maybe (Name, [Name])
isolatedFormula (ExtCond ext_e _)
    | [Prim op _, e1, e2] <- unApp ext_e
    , allowedOp op
    , Just (n, e) <- varEq e1 e2 = Just (n, map idName $ vars e)
    | App (Prim Not _) ext_e' <- ext_e
    , [Prim op _, e1, e2] <- unApp ext_e'
    , allowedOp op
    , Just (n, e) <- varEq e1 e2 = Just (n, map idName $ vars e)
    where
        varEq (Var (Id n _)) e = Just (n, e)
        varEq e (Var (Id n _)) = Just (n, e)
        varEq _ _ = Nothing

        allowedOp Eq = True
        allowedOp Neq = True
        allowedOp Lt = True
        allowedOp Gt = True
        allowedOp Le = True
        allowedOp Ge = True
        allowedOp _ = False
isolatedFormula _ = Nothing        

-- adapted from https://github.com/haskell/containers/issues/978
cycleExists :: Ord a => [(a, [a])] -> Bool
cycleExists tuples = any (uncurry elem) tuples ||
    -- There's a cycle if one of the strongly connected components has more than one node
    any ((> 1) . length . flattenSCC)
       -- Generate strongly connected components from edges
       (stronglyConnComp $
        -- Create edges by converting a tuple (a, b) to (a, a, [b]) to reflect a -> b
        map (\(a, b) -> (a, a, b)) tuples)

uniq :: Ord a => [a] -> Bool
uniq = comp . sort
    where
        comp [] = True
        comp [_] = True
        comp (x:y:xs) 
            | x == y = False
            | otherwise = comp (y : xs)

-- | A solver to time the runtime of other solvers
data TimeSolver s = TimeSolver
                        String -- ^ Prefix for output string
                        (IORef TimeSpec) -- ^ Timer
                        s -- ^ Underlying solver to count invocations of

-- | A solver to time the runtime of other solvers
timeSolver :: String -- ^ Prefix for output string
           -> s
           -> IO (TimeSolver s)
timeSolver pre_s s = do
    zero <- newIORef 0
    return (TimeSolver pre_s zero s)

-- | Lift timeSolver into a SomeSolver.
timeSomeSolver :: String  -- ^ Prefix for output string
               -> SomeSolver
               -> IO SomeSolver
timeSomeSolver pre_s (SomeSolver s) = return . SomeSolver =<< timeSolver pre_s s

instance Solver s => Solver (TimeSolver s) where
    check (TimeSolver _ ts solver) s pc = do
        st <- getTime Realtime
        r <- check solver s pc
        en <- getTime Realtime
        modifyIORef ts (+ (en - st))
        return r
    solve (TimeSolver _ ts solver) s b is pc = do
        st <- getTime Realtime
        r <- solve solver s b is pc
        en <- getTime Realtime
        modifyIORef ts (+ (en - st))
        return r
    close (TimeSolver pre_s io_ts solver) = do
        close solver
        ts <- readIORef io_ts
        let t = (fromInteger (toNanoSecs ts)) / (10 ^ (9 :: Int) :: Double)
        putStrLn $ pre_s ++ " Solving Time: " ++ show t

-- | A solver to count the number of solver calls
data CallsSolver s = CallsSolver
                            String -- ^ Prefix for output string
                            (IORef Int) -- ^ Counter
                            s -- ^ Underlying solver to count invocations of

-- | A solver to count the number of solver calls
callsSolver :: String  -- ^ Prefix for output string
            -> s
            -> IO (CallsSolver s)
callsSolver pre_s s = do
    zero <- newIORef 0
    return (CallsSolver pre_s zero s)

-- | Lift callsSolver into a SomeSolver.
callsSomeSolver :: String  -- ^ Prefix for output string
                -> SomeSolver
                -> IO SomeSolver
callsSomeSolver pre_s (SomeSolver s) = return . SomeSolver =<< callsSolver pre_s s

instance Solver s => Solver (CallsSolver s) where
    check (CallsSolver _ c solver) s pc = do
        r <- check solver s pc
        modifyIORef c (+ 1)
        return r
    solve (CallsSolver _ c solver) s b is pc = do
        r <- solve solver s b is pc
        modifyIORef c (+ 1)
        return r
    close (CallsSolver pre_s io_c solver) = do
        close solver
        c <- readIORef io_c
        putStrLn $ pre_s ++ " Solver Calls: " ++ show c
