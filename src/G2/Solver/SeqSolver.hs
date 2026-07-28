{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.SeqSolver (CheckUnsatSeq (..)) where

import G2.Language
import qualified G2.Language.ExprEnv as E
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
        putStrLn "GOT e1 e2"
        len_res <- checkLengths solver s e1 e2 pc pcs
        elem_res <- checkElems solver s e1 e2 pc pcs
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

checkLengths :: Solver solver => solver -> State t -> Expr -> Expr -> PathCond -> PathConds -> IO (Result () () ())
checkLengths solver s e1 e2 pc pcs = do
    let diff_length = mkApp [ Prim Neq TyUnknown
                            , App (Prim StrLen TyUnknown) e1 
                            , App (Prim StrLen TyUnknown) e2]
        diff_length_pc = ExtCond diff_length True
        pcs_with_diff_length = PC.insert diff_length_pc $ PC.filter (/= pc) pcs
        pcs_adj = convertMapEqsToLenEqs pcs_with_diff_length
    check solver s pcs_adj

convertMapEqsToLenEqs :: PathConds -> PathConds
convertMapEqsToLenEqs = PC.map go
    where
        go (ExtCond e True)
            | [Prim Eq _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, _, _ ] <- unApp eq_e2 =
                ExtCond
                (mkApp [ Prim Eq TyUnknown
                      , App (Prim StrLen TyUnknown) eq_e1
                      , App (Prim StrLen TyUnknown) eq_e2 ])
                True
        go pc = pc

checkElems :: Solver solver => solver -> State t -> Expr -> Expr -> PathCond -> PathConds -> IO (Result () () ())
checkElems solver s@(State { expr_env = eenv, known_values = kv }) e1 e2 pc pcs = do
    let elem_ind = Id (Name "ELEM_IND_!!_G2_!!" Nothing 0 Nothing) TyLitInt
        s' = s { expr_env = E.insertSymbolic elem_ind eenv }

        gt_0 = ExtCond (mkApp [Prim Le TyUnknown, Lit (LitInt 0), Var elem_ind]) True
        lt_len = ExtCond (mkApp [Prim Lt TyUnknown, Var elem_ind, App (Prim StrLen TyUnknown) e1]) True
        same_len = ExtCond
                    (mkApp [ Prim Eq TyUnknown
                          , App (Prim StrLen TyUnknown) e1
                          , App (Prim StrLen TyUnknown) e2])
                    True
        diff_elem = ExtCond
                    (mkApp [ Prim Neq TyUnknown
                          , mkApp [Prim SeqNth TyUnknown, e1, Var elem_ind]
                          , mkApp [Prim SeqNth TyUnknown, e2, Var elem_ind]])
                    True
        pcs_with_diff_elem = PC.insert gt_0
                           . PC.insert lt_len
                           . PC.insert same_len
                           . PC.insert diff_elem
                           $ PC.filter (/= pc) pcs

        ind_into = computeIndIntos kv elem_ind e1
                ++ computeIndIntos kv elem_ind e2
                ++ [ (e1, Var elem_ind)
                   , (e2, Var elem_ind) ]
        
        pcs_adj = convertAllToSeqNth kv ind_into
                $ convertMapWithSeqNth ind_into pcs_with_diff_elem

    check solver s' pcs_adj

computeIndIntos :: KnownValues -> Id -> Expr -> [(Expr, Expr)]
computeIndIntos kv elem_ind e
    | [ Prim StrAppend _, App (Prim SeqUnit _) _, e2 ] <- unApp $ consToSeqUnit kv e =
        [(e2, mkApp [Prim Minus TyUnknown, Var elem_ind, Lit (LitInt 1)])]
    | otherwise = []

consToSeqUnit :: KnownValues -> Expr -> Expr
consToSeqUnit kv (App (App (App (Data dc) _) x) ys) | dc_name dc == KV.dcCons kv =
    let xs = App (Prim SeqUnit TyUnknown) x in
    mkApp [Prim StrAppend TyUnknown, xs, ys]
consToSeqUnit _ e = e

convertMapWithSeqNth :: [(Expr, Expr)] -> PathConds -> PathConds
convertMapWithSeqNth ind_intos = PC.map go
    where
        go (ExtCond e True)
            | [Prim Eq _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, f, lst ] <- unApp eq_e2
            , Just ind_into_lst <- lookup lst ind_intos
             =
                let
                    nth_eq = mkApp [ Prim Eq TyUnknown
                                   , mkApp [Prim SeqNth TyUnknown, eq_e1, ind_into_lst]
                                   , App f $ mkApp [Prim SeqNth TyUnknown, lst, ind_into_lst ]
                                   ]
                    same_len = mkApp [ Prim Eq TyUnknown
                                     , App (Prim StrLen TyUnknown) eq_e1
                                     , App (Prim StrLen TyUnknown) lst]
                    anded = mkApp [Prim And TyUnknown, nth_eq, same_len]
                in
                ExtCond anded True

        go pc = pc

convertAllToSeqNth :: KnownValues -> [(Expr, Expr)] -> PathConds -> PathConds
convertAllToSeqNth kv ind_intos = PC.map go
    where
        go (ExtCond e True)
            | [Prim FoldLeft _, f, Data dc, lst] <- unApp e
            , dc_name dc == KV.dcTrue kv
            , Just ind_into <- lookup lst ind_intos
            , Just f' <- getBodyAll kv f
             =
                ExtCond
                (mkApp [ f'
                       , mkApp [Prim SeqNth TyUnknown, lst, ind_into ]
                       ])
                True

        go pc = pc
    
-- | Get the body of an `all` fold
getBodyAll :: KnownValues
           -> Expr -- ^ Function being folded over
           -> Maybe Expr
getBodyAll kv (Lam _ (Id col_v1 _) inner_l@(Lam _ (Id _ _) e))
    | [Prim And _, e1, e2] <- unApp $ makeAndRightAssoc e
    , accumTrue kv col_v1 e1
    , col_v1 `notElem` varNames e2 = Just $ replaceVar col_v1 (mkTrue kv) inner_l
getBodyAll _ _ = Nothing

accumTrue :: KnownValues -> Name -> Expr -> Bool
accumTrue _ n (Var (Id n1 _)) = n == n1
accumTrue kv n e | [Prim Eq _, Var (Id n1 _), Data dc] <- unApp e
                 , n == n1
                 , dc_name dc == KV.dcTrue kv = True
accumTrue _ _ _ = False

makeAndRightAssoc :: Expr -> Expr
makeAndRightAssoc
    (App 
        (App
            (Prim prim1 t1)
            (App (App (Prim prim2 _) e1) e2)
        )
    e3) | prim1 == And, prim2 == And =
        makeAndRightAssoc $ App
            (App (Prim prim1 t1) e1)
            (App (App (Prim prim1 t1) e2) e3)
makeAndRightAssoc e = e
