{-# LANGUAGE BangPatterns, LambdaCase, MultiWayIf, OverloadedStrings, TupleSections, ViewPatterns #-}

module G2.Solver.SeqSolver (CheckUnsatSeq (..)) where

import G2.Execution.PrimitiveEval
import G2.Language hiding (mkSeqLen)
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import G2.Lib.Printers
import G2.Solver

import Control.Applicative
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified G2.Data.UnionFind as UF

newtype CheckUnsatSeq solver = CheckUnsatSeq solver

-- | Attempt to prove that an inequality between two sequences is unsatisfiable
instance Solver solver => Solver (CheckUnsatSeq solver) where
    check (CheckUnsatSeq solver) s pc = do
        r1 <- foldExcludedUnsat solver s pc
        case r1 of
            UNSAT _ -> return r1
            _ -> do
                r2 <- checkUnsat solver s pc
                case r2 of
                    UNSAT _ -> return r2
                    _ -> check solver s pc

    solve (CheckUnsatSeq solver) = solve solver
    
    close (CheckUnsatSeq solver) = close solver

------------------------------------------------------------------------------
-- Length and different element
------------------------------------------------------------------------------

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
        -- putStrLn "CHECKING UNSAT"
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
checkLengths solver s@(State { known_values = kv, tyvar_env = tv_env }) e1 e2 pc pcs = do
    let diff_length = mkApp [ Prim Neq TyUnknown
                            , mkSeqLen kv tv_env e1 
                            , mkSeqLen kv tv_env e2]
        diff_length_pc = ExtCond diff_length True
        pcs_with_diff_length = PC.insert diff_length_pc $ PC.filter (/= pc) pcs
        pcs_adj = convertMapEqsToLenEqs s pcs_with_diff_length
    check solver s pcs_adj

-- | Simplify
--     xs == map f ys
-- to
--     seq.len xs == seq.len ys
convertMapEqsToLenEqs :: State t -> PathConds -> PathConds
convertMapEqsToLenEqs (State { known_values = kv, tyvar_env = tv_env }) = PC.map go
    where
        go (ExtCond e True)
            | [Prim Eq _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, _, _ ] <- getMap eq_e2 =
                ExtCond
                (mkApp [ Prim Eq TyUnknown
                       , mkSeqLen kv tv_env eq_e1
                       , mkSeqLen kv tv_env eq_e2 ])
                True
        go pc = pc

-- | Given that two lists `xs` and `ys` must be the same length (a condition we check via `checkLengths`),
-- check if there is some index `i` such that `xs !! i /= ys !! i`
checkElems :: Solver solver => solver -> State t -> Expr -> Expr -> PathCond -> PathConds -> IO (Result () () ())
checkElems solver s@(State { expr_env = eenv, known_values = kv, tyvar_env = tv_env }) e1 e2 pc pcs = do
    let elem_ind = Id (Name "ELEM_IND_!!_G2_!!" Nothing 0 Nothing) TyLitInt
        s' = s { expr_env = E.insertSymbolic elem_ind eenv }

        -- i must be between the beginning and end of the list
        gt_0 = ExtCond (mkApp [Prim Le TyUnknown, Lit (LitInt 0), Var elem_ind]) True
        lt_len = ExtCond (mkApp [Prim Lt TyUnknown, Var elem_ind, mkSeqLen kv tv_env e1]) True
        same_len = ExtCond
                    (mkApp [ Prim Eq TyUnknown
                          , mkSeqLen kv tv_env e1
                          , mkSeqLen kv tv_env e2])
                    True
        diff_elem = ExtCond
                    (mkApp [ Prim Neq TyUnknown
                          , mkSeqNth kv tv_env e1 (Var elem_ind)
                          , mkSeqNth kv tv_env e2 (Var elem_ind)])
                    True
        pcs_with_diff_elem = PC.insert gt_0
                           . PC.insert lt_len
                           . PC.insert same_len
                           . PC.insert diff_elem
                           $ PC.filter (/= pc) pcs

        ind_into = HM.fromList $
                   [ (e1, HS.singleton $ Var elem_ind)
                   , (e2, HS.singleton $ Var elem_ind) ]
    prop_ind_into <- propagateIndInto s' ind_into pcs_with_diff_elem

    let pcs_adj = convertAllToSeqNth s prop_ind_into
                $ convertMapWithSeqNth s prop_ind_into pcs_with_diff_elem

    check solver s' pcs_adj

consToSeqUnit :: KnownValues -> Expr -> Expr
consToSeqUnit kv (App (App (App (Data dc) _) x) ys) | dc_name dc == KV.dcCons kv =
    let xs = App (Prim SeqUnit TyUnknown) x in
    mkApp [Prim StrAppend TyUnknown, xs, ys]
consToSeqUnit _ e = e

-- | Converting map equality checks into checks on a specific element.
convertMapWithSeqNth :: State t -> IndInto -> PathConds -> PathConds
convertMapWithSeqNth (State { known_values = kv, tyvar_env = tv_env }) ind_intos = PC.concatMapHashedPCs go
    where
        go (PC.unhashedPC -> ExtCond e True)
            | Just (f, lst, eq_e1) <- eqToMap e
            , m_ind_into_eq_e1 <- HM.lookup eq_e1 ind_intos
            , m_ind_into_lst <- HM.lookup lst ind_intos
            , Just ind_into <- m_ind_into_eq_e1 <|> m_ind_into_lst
             =
                let
                    nth_eq = HS.map (\ii -> mkApp [ Prim Eq TyUnknown
                                                  , mkSeqNth kv tv_env eq_e1 ii
                                                  , App f $ mkSeqNth kv tv_env lst ii
                                                  ]) ind_into
                    same_len = mkApp [ Prim Eq TyUnknown
                                     , mkSeqLen kv tv_env eq_e1
                                     , mkSeqLen kv tv_env lst]
                in
                map PC.hashedPC . map (flip ExtCond True) $ same_len:HS.toList nth_eq
            | [Prim StrPrefixOf _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, f, lst ] <- getMap eq_e1
            , Just ind_into <- HM.lookup lst ind_intos =
                let
                    nth_eq = HS.map (\ii -> mkApp [ Prim Eq TyUnknown
                                                  , mkSeqNth kv tv_env eq_e2 ii
                                                  , App f $ mkSeqNth kv tv_env lst ii
                                                  ]) ind_into
                    ge_len = mkApp [ Prim Ge TyUnknown
                                   , mkSeqLen kv tv_env eq_e2
                                   , mkSeqLen kv tv_env lst]
                in
                map PC.hashedPC . map (flip ExtCond True) $ ge_len:HS.toList nth_eq
            | [Prim StrPrefixOf _, eq_e1, eq_e2] <- unApp e
            , [Prim Map _, f, lst ] <- getMap eq_e2
            , Just ind_into <- HM.lookup lst ind_intos =
                let
                    nth_eq = HS.map (\ii -> mkApp [ Prim Eq TyUnknown
                                                  , mkSeqNth kv tv_env eq_e1 ii
                                                  , App f $ mkSeqNth kv tv_env lst ii
                                                  ]) ind_into
                    le_len = mkApp [ Prim Le TyUnknown
                                   , mkSeqLen kv tv_env eq_e1
                                   , mkSeqLen kv tv_env lst]
                in
                map PC.hashedPC . map (flip ExtCond True) $ le_len:HS.toList nth_eq

        go pc = [pc]

getMap :: Expr -> [Expr]
getMap e
    | es@[Prim Map _, _, _] <- unApp e = es
    | [Prim StrAppend _, l1, l2] <- unApp e
    , [Prim Map t, f1, e1] <- unApp l1
    , [Prim Map _, f2, e2] <- unApp l2
    , f1 == f2 = [Prim Map t, f1, mkApp [Prim StrAppend TyUnknown, e1, e2]]
    | otherwise = []

-- Given (map f ys == xs) returns (f, ys, xs)
eqToMap :: Expr -> Maybe (Expr, Expr, Expr)
eqToMap e
    | [Prim Eq _, eq_e1, eq_e2] <- unApp e
    , [Prim Map _, f, lst ] <- getMap eq_e2 = Just (f, lst, eq_e1)
    | [Prim Eq _, eq_e1, eq_e2] <- unApp e
    , [Prim Map _, f, lst ] <- getMap eq_e1 = Just (f, lst, eq_e2)
    | otherwise = Nothing
    
-- | If we have fold corresponding to the `all` function, then the condition that the require
-- must hold for the i^th element
convertAllToSeqNth :: State t -> IndInto -> PathConds -> PathConds
convertAllToSeqNth (State { known_values = kv, tyvar_env = tv_env }) ind_intos = PC.concatMapHashedPCs go
    where
        go (PC.unhashedPC -> ExtCond e True)
            | [Prim FoldLeft _, f, Data dc, lst] <- unApp e
            , dc_name dc == KV.dcTrue kv
            , Just ind_into <- HM.lookup lst ind_intos
            , Just f' <- getBodyAll kv f
             =
                let f_seq_nths = HS.map (App f' . mkSeqNth kv tv_env lst) ind_into in
                map PC.hashedPC . map (flip ExtCond True) $ HS.toList f_seq_nths
        go pc = [pc]
    
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

------------------------------------------------------------------------------
-- Fold excluded element
------------------------------------------------------------------------------

-- Rewrite folds enforcing that a specific elements cannot be in a list to check
-- the list at specific elements from other constraints.

foldExcludedUnsat :: Solver solver => solver -> State t -> PathConds -> IO (Result () () ())
foldExcludedUnsat solver s@(State { known_values = kv }) pcs
    | Just _ <- PC.firstJust (getFoldExcluding kv) pcs = do
        putStrLn "CHECKING UNSAT foldExcludedUnsat"

        let nth_inds = HM.unionWith HS.union (listStart kv pcs) (nthFrom pcs)
        let pretty_inds = prettyIndInto (setPrintUnique True $ mkPrettyGuide ()) s nth_inds
        -- putStrLn "\nnth_inds = "
        -- T.putStrLn pretty_inds

        prop_nth_inds <- propagateIndInto s nth_inds pcs
        -- let pretty_inds = prettyIndInto (setPrintUnique True $ mkPrettyGuide ()) s prop_nth_inds
        -- putStrLn "prop_nth_inds = "
        -- T.putStrLn pretty_inds

        let pcs_adj = simplifyLams
                    . convertMapWithSeqNth s prop_nth_inds
                    $ convertAllToSeqNth s prop_nth_inds pcs

        check solver s pcs_adj
    | otherwise = return $ SAT ()

getFoldExcluding :: KnownValues -> PathCond -> Maybe (PathCond, Expr, Expr)
getFoldExcluding kv pc@(ExtCond e True)
    | [ Prim FoldLeft _, f@(Lam _ _ (Lam _ val_i f_body)), init_e, lst] <- unApp e
    , Data dc <- init_e, dc_name dc == KV.dcTrue kv
    , Just _ <- getBodyAll kv f -- Make sure we have an "all"
    , conj <- getConjoined f_body
    , neq_chck:_ <- filter isNeq conj = Just (pc, lst, Lam TermL val_i neq_chck)
    | [Prim Not _, con] <- unApp e
    , [Prim StrContains _, _, _] <- unApp con = Just undefined 
getFoldExcluding _ _ = Nothing

listStart :: KnownValues -> PathConds -> IndInto
listStart kv = HM.fromListWith (HS.union) . evalASTs go
    where
        go e | [Prim StrAppend _, _, _] <- unApp $ consToSeqUnit kv e = [(e, HS.singleton . Lit $ LitInt 0)]
             | otherwise = []

nthFrom :: PathConds
        -> IndInto -- ^ (List, Index)
nthFrom = HM.fromListWith (HS.union) . evalASTs go
    where
        go e 
            | [Prim SeqNth _, xs, i] <- unApp e = [(xs, HS.singleton i)]
            | otherwise = []

isNeq :: Expr -> Bool
isNeq e
    | [Prim Neq _, _, _] <- unApp e = True
    | otherwise= False

------------------------------------------------------------------------------
-- Ind Into
------------------------------------------------------------------------------

type IndInto = HM.HashMap Expr (HS.HashSet Expr)

propagateIndInto :: State t -> IndInto -> PathConds -> IO IndInto
propagateIndInto = propagateIndInto' 3

propagateIndInto' :: Int -> State t -> IndInto -> PathConds -> IO IndInto
propagateIndInto' !n s@(State { known_values = kv, tyvar_env = tv_env }) ind_into pcs =
    let
        new_ind_app = HM.fromListWith HS.union $ propagateIndApp kv tv_env ind_into pcs
        new_ind_map = HM.fromListWith HS.union $ propagateIndMap kv ind_into pcs
        new_ind_eq = HM.fromListWith HS.union . concatMap (propagateIndEq kv ind_into) . PC.toList $ pcs
        unionApp = foldl' (HM.unionWith HS.union) HM.empty

        new_ind_into = filterRedundant kv pcs $ unionApp [new_ind_map, new_ind_app, new_ind_eq]
        all_ind_into = HM.unionWith HS.union ind_into new_ind_into
    in
    case ind_into == all_ind_into of
        False | n > 0 -> do
            -- let pretty_inds = prettyIndInto (setPrintUnique True $ mkPrettyGuide ()) s new_ind_into
            -- putStrLn "\niteration = "
            -- T.putStrLn pretty_inds
            propagateIndInto' (n - 1) s all_ind_into pcs
        _ -> do
            -- let pretty_inds = prettyIndInto (setPrintUnique True $ mkPrettyGuide ()) s all_ind_into
            -- putStrLn "\nfinal = "
            -- T.putStrLn pretty_inds
            
            return all_ind_into

-- | Propagate across ++.
-- ind(xs) = n <-> ind(xs ++ ys) = n,
-- ind(ys) = n <-> ind(xs ++ ys) = n + length xs
propagateIndApp :: KnownValues -> TyVarEnv -> IndInto -> PathConds -> [(Expr, HS.HashSet Expr)]
propagateIndApp kv tv_env ind_into = evalASTs go
    where
        go e
            | [Prim StrAppend _, xs, ys] <- unApp $ consToSeqUnit kv e =
                let
                    xs_to_whole = case HM.lookup xs ind_into of
                                    Nothing -> []
                                    Just elem_ind -> [(e, elem_ind)]

                    ys_to_whole = case HM.lookup ys ind_into of
                                    Nothing -> []
                                    Just elem_ind -> [(e, HS.map (\ii -> mkSmartPlus
                                                                               ii
                                                                               $ mkSeqLen kv tv_env xs) elem_ind)]
                    whole_to_xs_ys = case HM.lookup e ind_into of
                                            Nothing -> []
                                            Just elem_ind ->
                                                [ (xs, elem_ind)
                                                , (ys, HS.map (\ii -> mkSmartMinus
                                                                            ii
                                                                            $ mkSeqLen kv tv_env xs) elem_ind)
                                                ]
                in
                xs_to_whole ++ ys_to_whole ++ whole_to_xs_ys
            | otherwise = []

-- | Propagate across ==.
-- xs == ys and ind(xs) = n -> ind(ys) = n
-- xs == ys and ind(xs) = n -> ind(ys) = n
propagateIndEq :: KnownValues -> IndInto -> PathCond -> [(Expr, HS.HashSet Expr)]
propagateIndEq kv ind_intos (ExtCond e True) =
    let
        eq_list_prop = case unApp $ consToSeqUnit kv e of
                            [ Prim Eq _, lst1, lst2 ] ->
                                catMaybes [fmap (lst1,) (HM.lookup lst2 ind_intos), fmap (lst2,) (HM.lookup lst1 ind_intos)]
                                -- propEqApp kv tv_env ind_intos lst1 lst2 ++ propEqApp kv tv_env ind_intos lst2 lst1
                            _ -> []
    in
    eq_list_prop
propagateIndEq _ _ _ = []

-- | Propagate across map.
-- ind(xs) = n <-> ind(map f xs) = n,
-- ind(map f xs) = n <-> ind(xs) = n
propagateIndMap :: KnownValues -> IndInto -> PathConds -> [(Expr, HS.HashSet Expr)]
propagateIndMap kv ind_into = evalASTs go
    where
        go e
            | [Prim Map _, _, xs] <- unApp $ consToSeqUnit kv e =
                let
                    xs_to_map = case HM.lookup xs ind_into of
                                    Nothing -> []
                                    Just elem_ind -> [(e, elem_ind)]
                    map_to_xs = case HM.lookup e ind_into of
                                    Nothing -> []
                                    Just elem_ind -> [(xs, elem_ind)]

                in
                xs_to_map ++ map_to_xs
            | otherwise = []

-- propEqApp :: KnownValues -> TyVarEnv -> IndInto -> Expr -> Expr -> [(Expr, HS.HashSet Expr)]
-- propEqApp kv tv_env ind_intos lst1 lst2
--     | [ Prim StrAppend _, e1@(Prim SeqUnit _), e2 ] <- unApp $ consToSeqUnit kv lst1
--     , Just ind_into <- HM.lookup lst2 ind_intos =
--         [ (e1, ind_into)
--         , (e2, HS.map (\ii -> mkSmartMinus
--                                     ii
--                                     $ Lit (LitInt 1)) ind_into)
--         ]
--     | [ Prim StrAppend _, e1, e2 ] <- unApp $ consToSeqUnit kv lst1
--     , Just ind_into <- HM.lookup lst2 ind_intos =
--         [ (e1, ind_into)
--         , (e2, HS.map (\ii -> mkSmartMinus
--                                     ii
--                                     $ mkSeqLen kv tv_env e1) ind_into)
--         ]
--     | otherwise = []

-- Filter out redundant indicies. In particular, (str.len xs) is guaranteed to be off the edge of xs
filterRedundant :: KnownValues -> PathConds -> IndInto -> IndInto
filterRedundant kv pcs =
    let eq_len = getEqLengths pcs in
    HM.filter (not . HS.null) . HM.mapWithKey (filterRedundant' eq_len kv)

filterRedundant' :: UF.UnionFind Expr -> KnownValues -> Expr -> HS.HashSet Expr -> HS.HashSet Expr
filterRedundant' eq_len kv e1 = HS.filter (not . isRedundant)
    where
        isRedundant e 
            | [Prim Mult _, _, App (Prim StrLen _) e2] <- unApp e = UF.find e1 eq_len == UF.find e2 eq_len
        isRedundant (App (Prim StrLen _) e2) = UF.find e1 eq_len == UF.find e2 eq_len
        isRedundant e | negNum e = True
        isRedundant e2
            | [Prim Minus _, Lit (LitInt 0), e2'] <- unApp e2
            , posNum e2' = True
        isRedundant _ = False

        posNum (Lit (LitInt n)) = n > 0
        posNum (App (Prim StrLen _) e) | nonEmptyList e = True
        posNum _ = False

        negNum (Lit (LitInt n)) = n < 0
        negNum _ = False

        nonEmptyList e | [Prim StrAppend _, app_e1, app_e2] <- unApp e = nonEmptyList app_e1 || nonEmptyList app_e2
                       | [Prim SeqUnit _, _] <- unApp e = True
                       | Data dc:_ <- unApp e = dc_name dc == KV.dcCons kv
        nonEmptyList _ = False

getEqLengths :: PathConds -> UF.UnionFind Expr
getEqLengths = foldl' go UF.empty . PC.toList
    where
        go uf (ExtCond e True)
            | [Prim Eq _
            , App (Prim StrLen _) lst1
            , App (Prim StrLen _) lst2] <- unApp e = UF.union lst1 lst2 uf
        go uf _ = uf

mkSmartPlus :: Expr -> Expr -> Expr
mkSmartPlus e1 (Lit (LitInt 0)) = e1
mkSmartPlus (Lit (LitInt 0)) e2 = e2
mkSmartPlus e1 e2
    -- | [Prim Minus _, e_add1, e_add2] <- unApp e1
    -- , e_add2 == e2 = e_add1
    | otherwise = reduce $ mkApp [ Prim Plus TyUnknown, e1, e2]

mkSmartMinus :: Expr -> Expr -> Expr
mkSmartMinus e1 (Lit (LitInt 0)) = e1
mkSmartMinus e1 e2
    -- | [Prim Plus _, e_add1, e_add2] <- unApp e1
    -- , e_add1 == e2 = e_add2
    | otherwise = reduce $ mkApp [ Prim Minus TyUnknown, e1, e2]

reduce :: Expr -> Expr
reduce e = 
    let
        (es, ls) = partition (not . isLitInt) $ summed e
        cs = foldl' countE HM.empty es
        total_l = foldl' sumL 0 ls

        cs_mult = mapMaybe (\(e', l) -> case l of
                                        0 -> Nothing
                                        1 -> Just e'
                                        _ -> Just $ mkApp [Prim Mult TyUnknown, Lit (LitInt l), e'] ) $ HM.toList cs
    in
    case cs_mult of
        [] -> Lit (LitInt total_l)
        c:cs' -> 
            let e_sum = foldl' (\e1 e2 -> mkApp [Prim Plus TyUnknown, e1, e2]) c cs'
                res = case total_l of
                            0 -> e_sum
                            _ -> mkApp [Prim Plus TyUnknown, e_sum, Lit (LitInt total_l)]
            in
            res
    where
        isLitInt (Lit (LitInt _)) = True
        isLitInt _ = False
        
        sumL c (Lit (LitInt l)) = c + l
        sumL _ _ = error "reduce: sumL passed unexpected value"

        countE hm (App (Prim Negate _) e') = HM.insertWith (+) e' (-1) hm
        countE hm e' 
            | [Prim Mult _, Lit (LitInt l), e''] <- unApp e' = HM.insertWith (+) e'' l hm
        countE hm e' = HM.insertWith (+) e' 1 hm

        summed e'
            | [Prim Plus _, e1, e2] <- unApp e' = summed e1 ++ summed e2
            | [Prim Minus _, e1, e2] <- unApp e' = summed e1 ++ map neg (summed e2)
            | otherwise = [e']

        neg (Lit (LitInt x)) = Lit . LitInt $ -x
        neg (App (App (Prim Mult TyUnknown) (Lit (LitInt l))) e') = App (App (Prim Mult TyUnknown) (Lit $ LitInt (-l))) e'
        neg e' = App (App (Prim Mult TyUnknown) (Lit $ LitInt (-1))) e'

-- type IndInto = HM.HashMap Expr (HS.HashSet Expr)

prettyIndInto :: PrettyGuide -> State t -> IndInto -> T.Text
prettyIndInto pg s = 
      T.intercalate "\n"
    . map (\(lst, inds) -> printHaskellPG pg s lst <> " ->\n\t"
                           <> T.intercalate "\n\t" (map (printHaskellPG pg s) $ HS.toList inds))
    . HM.toList

------------------------------------------------------------------------------
-- Constructing primitives
------------------------------------------------------------------------------

mkSeqLen :: KnownValues -> TyVarEnv -> Expr -> Expr
mkSeqLen _ _ (App (Prim SeqUnit _) _) = Lit (LitInt 1)
mkSeqLen kv _ e | [Prim Map _, _, e'] <- unApp e
                , Just xs <- toExprList kv e' = Lit . LitInt $ genericLength xs
mkSeqLen kv _ e | Just xs <- toExprList kv e = Lit . LitInt $ genericLength xs
mkSeqLen kv tv_env e =
    let t = TyFun (typeOf tv_env e) (tyBool kv) in
    App (Prim StrLen t) e

mkSeqNth :: KnownValues -> TyVarEnv -> Expr -> Expr -> Expr
mkSeqNth kv tv_env lst ind =
    let t = TyFun (typeOf tv_env lst) (TyFun TyLitInt (tyBool kv)) in
    mkApp [Prim SeqNth t, lst, ind]
