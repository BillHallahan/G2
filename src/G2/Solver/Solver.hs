{-# LANGUAGE RankNTypes #-}

module G2.Solver.Solver ( Solver (..)
                                  , Result (..)
                                  , GroupRelated (..)
                                  , CombineSolvers (..)) where

import G2.Language
import qualified G2.Language.PathConds as PC
import qualified Data.Map as M

-- | The result of a Solver query
data Result = SAT
            | UNSAT
            | Unknown String
            deriving (Show, Eq)

-- | Defines an interface to interact with Solvers
class Solver solver where
    -- | Checks if the given `PathConds` are satisfiable
    check :: forall t . solver -> State t -> PathConds -> IO Result
    -- | Checks if the given `PathConds` are satisfiable, and, if yes, gives a `Model`
    -- The model must contain, at a minimum, a value for each passed `Id`
    solve :: forall t . solver -> State t -> [Id] -> PathConds -> IO (Result, Maybe Model)

-- | Splits path constraints before sending them to the rest of the solvers
data GroupRelated a = GroupRelated a

checkRelated :: Solver a => a -> State t -> PathConds -> IO Result
checkRelated solver s pc = do
    checkRelated' solver s $ PC.relatedSets (known_values s) pc

checkRelated' :: Solver a => a -> State t -> [PathConds] -> IO Result
checkRelated' _ _ [] = return SAT
checkRelated' solver s (p:ps) = do
    c <- check solver s p
    case c of
        SAT -> checkRelated' solver s ps
        r -> return r

solveRelated :: Solver a => a -> State t -> [Id] -> PathConds -> IO (Result, Maybe Model)
solveRelated solver s is pc = do
    solveRelated' solver s M.empty is $ PC.relatedSets (known_values s) pc

solveRelated' :: Solver a => a -> State t -> Model -> [Id] -> [PathConds] -> IO (Result, Maybe Model)
solveRelated' _ s m is [] =
    let 
        is' = filter (\i -> idName i `M.notMember` m) is
        nv = map (\(Id n t) -> (n, fst $ arbValue t (type_env s) (arb_value_gen s))) is'
        m' = foldr (\(n, v) -> M.insert n v) m nv
    in
    return (SAT, Just m')
solveRelated' solver s m is (p:ps) = do
    let is' = concat $ PC.map' (PC.varIdsInPC (known_values s)) p
    let is'' = ids p
    rm <- solve solver s is' p
    case rm of
        (SAT, Just m') -> solveRelated' solver s (M.union m m') (is ++ is'') ps
        rm' -> return rm'

instance Solver solver => Solver (GroupRelated solver) where
    check (GroupRelated s) = checkRelated s
    solve (GroupRelated s) = solveRelated s


-- | Allows solvers to be combined, to exploit different solvers abilities
-- to solve different kinds of constraints
data CombineSolvers a b = a :<? b -- ^ a :<? b - Try solver b.  If it returns Unknown, try solver a
                        | a :?> b -- ^ a :>? b - Try solver a.  If it returns Unknown, try solver b

checkWithEither :: (Solver a, Solver b) => a -> b -> State t -> PathConds -> IO Result
checkWithEither a b s pc = do
    ra <- check a s pc 
    case ra of
        SAT -> return SAT
        UNSAT -> return UNSAT
        Unknown ua -> do
            rb <- check b s pc
            case rb of
                Unknown ub -> return $ Unknown $ ua ++ ",\n" ++ ub
                rb' -> return rb'

solveWithEither :: (Solver a, Solver b) => a -> b -> State t -> [Id] -> PathConds -> IO (Result, Maybe Model)
solveWithEither a b s is pc = do
    ra <- solve a s is pc 
    case ra of
        (SAT, m) -> return (SAT, m)
        (UNSAT, m) -> return (UNSAT, m)
        (Unknown ua, _) -> do
            rb <- solve b s is pc
            case rb of
                (Unknown ub, _) -> return $ (Unknown $ ua ++ ",\n" ++ ub, Nothing)
                rb' -> return rb'

instance (Solver a, Solver b) => Solver (CombineSolvers a b) where
    check (a :<? b) = checkWithEither b a
    check (a :?> b) = checkWithEither a b

    solve (a :<? b) = solveWithEither b a
    solve (a :?> b) = solveWithEither a b
