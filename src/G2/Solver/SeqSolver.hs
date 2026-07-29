{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module G2.Solver.SeqSolver (CheckUnsatSeq (..)) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import G2.Solver

import Control.Applicative
import Data.List
import Data.Maybe
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
        let pcs' = PC.filter (\case (ExtCond e _) -> noMaps e; _ -> True) pcs
        res_no_maps <- check solver s pcs'
    
        case res_no_maps of
            UNSAT _ -> return $ UNSAT ()
            _ -> do
                len_res <- checkLengths solver s e1 e2 pc pcs
                case len_res of
                    UNSAT _ -> do
                        elem_res <- checkElems solver s e1 e2 pc pcs
                        case elem_res of
                            UNSAT _ -> return $ UNSAT ()
                            _ -> return $ Unknown "CheckUnsatSeq Solver" ()
                    _ -> return $ Unknown "CheckUnsatSeq Solver" ()
checkUnsat solver s pcs = do
    let pcs' = PC.filter (\case (ExtCond e _) -> noMaps e; _ -> True) pcs
    res <- check solver s pcs'
    case res of
        UNSAT _ -> return $ UNSAT ()
        _ -> return $ Unknown "CheckUnsatSeq Solver" ()

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

-- | Check unsatisfiability when just asserting that the lengths of sequences are the same
checkLengths :: Solver solver => solver -> State t -> Expr -> Expr -> PathCond -> PathConds -> IO (Result () () ())
checkLengths solver s e1 e2 pc pcs = do
    let diff_length = mkApp [ Prim Neq TyUnknown
                            , App (Prim StrLen TyUnknown) e1 
                            , App (Prim StrLen TyUnknown) e2]
        diff_length_pc = ExtCond diff_length True
        pcs_with_diff_length = PC.insert diff_length_pc $ PC.filter (/= pc) pcs
        pcs_adj = convertMapEqsToLenEqs pcs_with_diff_length
    check solver s pcs_adj

-- | Simplify
--     xs == map f ys
-- to
--     seq.len xs == seq.len ys
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

-- | Given that two lists `xs` and `ys` must be the same length (a condition we check via `checkLengths`),
-- check if there is some index `i` such that `xs !! i /= ys !! i`
checkElems :: Solver solver => solver -> State t -> Expr -> Expr -> PathCond -> PathConds -> IO (Result () () ())
checkElems solver s@(State { expr_env = eenv, known_values = kv }) e1 e2 pc pcs = do
    let elem_ind = Id (Name "ELEM_IND_!!_G2_!!" Nothing 0 Nothing) TyLitInt
        s' = s { expr_env = E.insertSymbolic elem_ind eenv }

        -- i must be between the beginning and end of the list
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
        prop_ind_into = ind_into ++ mapMaybe (propagateIndInto ind_into) (PC.toList pcs_with_diff_elem)
        
        pcs_adj = convertAllToSeqNth kv prop_ind_into
                $ convertMapWithSeqNth prop_ind_into pcs_with_diff_elem

    check solver s' pcs_adj

-- | If we have, for instance, `xs == x ++ xs'`, this figures out that `xs !! i` is the same as `xs' !! (i - 1)`
computeIndIntos :: KnownValues
                -> Id
                -> Expr
                -> [(Expr, Expr)] -- ^ maps list expressions to the relevant index of that list, i.e. xs -> i, xs' -> (i - 1)
computeIndIntos kv elem_ind e
    | [ Prim StrAppend _, App (Prim SeqUnit _) _, e2 ] <- unApp $ consToSeqUnit kv e =
        [(e2, mkApp [Prim Minus TyUnknown, Var elem_ind, Lit (LitInt 1)])]
    | otherwise = []

consToSeqUnit :: KnownValues -> Expr -> Expr
consToSeqUnit kv (App (App (App (Data dc) _) x) ys) | dc_name dc == KV.dcCons kv =
    let xs = App (Prim SeqUnit TyUnknown) x in
    mkApp [Prim StrAppend TyUnknown, xs, ys]
consToSeqUnit _ e = e

propagateIndInto :: [(Expr, Expr)] -> PathCond -> Maybe (Expr, Expr)
propagateIndInto ind_intos (ExtCond e True)
    | Just (_, lst, eq_e1) <- eqToMap e =
        case (lookup eq_e1 ind_intos, lookup lst ind_intos) of
            (Just ind_into, Nothing) -> Just (lst, ind_into)
            (Nothing, Just ind_into) -> Just (eq_e1, ind_into)
            _ -> Nothing
propagateIndInto _ _ = Nothing

-- | Converting map equality checks into checks on a specific element.
convertMapWithSeqNth :: [(Expr, Expr)] -> PathConds -> PathConds
convertMapWithSeqNth ind_intos = PC.map go
    where
        go (ExtCond e True)
            | Just (f, lst, eq_e1) <- eqToMap e
            , m_ind_into_eq_e1 <- lookup eq_e1 ind_intos
            , m_ind_into_lst <- lookup lst ind_intos
            , Just ind_into <- m_ind_into_eq_e1 <|> m_ind_into_lst
             =
                let
                    nth_eq = mkApp [ Prim Eq TyUnknown
                                   , mkApp [Prim SeqNth TyUnknown, eq_e1, ind_into]
                                   , App f $ mkApp [Prim SeqNth TyUnknown, lst, ind_into ]
                                   ]
                    same_len = mkApp [ Prim Eq TyUnknown
                                     , App (Prim StrLen TyUnknown) eq_e1
                                     , App (Prim StrLen TyUnknown) lst]
                    anded = mkApp [Prim And TyUnknown, nth_eq, same_len]
                in
                ExtCond anded True
            | [Prim StrPrefixOf _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, f, lst ] <- unApp eq_e1
            , Just ind_into <- lookup lst ind_intos =
                let
                    nth_eq = mkApp [ Prim Eq TyUnknown
                                   , mkApp [Prim SeqNth TyUnknown, eq_e2, ind_into]
                                   , App f $ mkApp [Prim SeqNth TyUnknown, lst, ind_into ]
                                   ]
                    ge_len = mkApp [ Prim Ge TyUnknown
                                     , App (Prim StrLen TyUnknown) eq_e2
                                     , App (Prim StrLen TyUnknown) lst]
                    anded = mkApp [Prim And TyUnknown, nth_eq, ge_len]
                in
                ExtCond anded True
        go pc = pc

-- Given (map f ys == xs) returns (f, ys, xs)
eqToMap :: Expr -> Maybe (Expr, Expr, Expr)
eqToMap e
    | [Prim Eq _, eq_e1, eq_e2] <- unApp e
    , [Prim Map _, f, lst ] <- unApp eq_e2 = Just (f, lst, eq_e1)
    | [Prim Eq _, eq_e1, eq_e2] <- unApp e
    , [Prim Map _, f, lst ] <- unApp eq_e1 = Just (f, lst, eq_e2)
    | otherwise = Nothing
    
-- | If we have fold corresponding to the `all` function, then the condition that the require
-- must hold for the i^th element
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
    | es <- getConjoined e
    , Just accum_e <- find (accumTrue kv col_v1) es
    , col_v1 `notElem` varNames (delete accum_e es) = Just $ replaceVar col_v1 (mkTrue kv) inner_l
getBodyAll _ _ = Nothing

accumTrue :: KnownValues -> Name -> Expr -> Bool
accumTrue _ n (Var (Id n1 _)) = n == n1
accumTrue kv n e | [Prim Eq _, Var (Id n1 _), Data dc] <- unApp e
                 , n == n1
                 , dc_name dc == KV.dcTrue kv = True
accumTrue _ _ _ = False

getConjoined :: Expr -> [Expr]
getConjoined e
    | [Prim And _, e1, e2] <- unApp e = getConjoined e1 ++ getConjoined e2
    | otherwise = [e]