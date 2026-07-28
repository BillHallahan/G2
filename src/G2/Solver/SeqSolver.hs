module G2.Solver.SeqSolver (CheckUnsatSeq (..)) where

import G2.Language
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import G2.Solver

import Data.Monoid

newtype CheckUnsatSeq solver = CheckUnsatSeq solver

-- | Attempt to prove that an inequality between two sequences is unsatisfiable
instance Solver solver => Solver (CheckUnsatSeq solver) where
    check (CheckUnsatSeq solver) s pc = do
        r <- checkUnsat solver s pc
        case r of
            UNSAT _ -> return r
            _ -> check solver s pc

    solve (CheckUnsatSeq solver) = solve solver
    
    close (CheckUnsatSeq solver) = close solver

-- The key idea is that, given two sequences xs and ys, the formula:
--     xs /= ys
-- is equivalent to
--     length xs /= length ys \/ (exists 0 <= i <= length xs . xs !! i /= ys !! i)
-- we try to prove formulas with sequence inequalities unsatisfiable using the above equivalence.
-- In particular, we generate TWO formulas-- one which asserts the sequences have different lengths,
-- one which asserts the sequences differ at some index.
-- We weaken both formulas by eliminating (some uses of) higher order functions map and fold
-- making the formula easier for Z3 to handle.
-- This means that the original formula implies the new formulas, i.e.
-- if the new formula is unsatisfiable, the original formula was unsatisfiable.

checkUnsat :: Solver solver => solver -> State t -> PathConds -> IO (Result () () ())
checkUnsat solver s@(State { known_values = kv, tyvar_env = tv_env }) pcs
    | Just (pc, e1, e2) <- PC.firstJust (getListInequality kv tv_env) pcs = do
        let diff_length = mkApp [ Prim Neq TyUnknown
                                , App (Prim StrLen TyUnknown) e1 
                                , App (Prim StrLen TyUnknown) e2]
            diff_length_pc = ExtCond diff_length True
            pcs_with_diff_length = PC.insert diff_length_pc $ PC.filter (/= pc) pcs
            pcs_adj = convertMapEqsToLenEqs e1 e2 pcs_with_diff_length
        putStrLn "GOT e1 e2"
        check solver s pcs_adj
        return $ Unknown "CheckUnsatSeq Solver" ()
checkUnsat _ _ _ = return $ Unknown "CheckUnsatSeq Solver" ()

getListInequality :: KnownValues -> TyVarEnv -> PathCond -> Maybe (PathCond, Expr, Expr)
getListInequality kv tv_env pc@(ExtCond (App (Prim Not _) e) True)
    | [Prim Eq _, e1, e2] <- unApp e
    , noMaps e1
    , noMaps e2
    , isListTy kv tv_env e1 = Just (pc, e1, e2)
getListInequality kv tv_env pc@(ExtCond e False)
    | [Prim Eq _, e1, e2] <- unApp e
    , noMaps e1
    , noMaps e2
    , isListTy kv tv_env e1 = Just (pc, e1, e2)
getListInequality _ _ _ = Nothing

noMaps :: Expr -> Bool
noMaps = not . getAny . evalASTs go
    where
        go (Prim Map _) = Any True
        go _ = Any False

isListTy :: KnownValues -> TyVarEnv -> Expr -> Bool
isListTy kv tv_env e =
    case typeOf tv_env e of
        TyApp (TyCon n _) _ -> n == KV.tyList kv
        _ -> False

convertMapEqsToLenEqs :: Expr -> Expr -> PathConds -> PathConds
convertMapEqsToLenEqs e1 e2 = PC.map go
    where
        go (ExtCond e True)
            | [Prim Eq _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, _, e_mapped ] <- unApp eq_e2 =
                ExtCond
                (mkApp [ Prim Eq TyUnknown
                      , App (Prim StrLen TyUnknown) eq_e1
                      , App (Prim StrLen TyUnknown) eq_e2 ])
                True
        go pc = pc