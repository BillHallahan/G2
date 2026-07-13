{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, OverloadedStrings, TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , SomeSimplifier (..)
                            , (:>>) (..)
                            , IdSimplifier (..)
                            , ArithSimplifier (..)
                            , BoolSimplifier (..)
                            , StringSimplifier (..)
                            , FloatSimplifier (..)
                            , EqualitySimplifier (..)
                            , LitConc (..)
                            , LamVarSimplifier (..)
                            , ConstSimplifier (..)
                            , HigherOrderSimplifier (..)
                            ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Typing as T
import qualified Data.HashSet as HS
import qualified Data.List as L

class Simplifier simplifier where
    -- | Simplifies a PC, by converting it into one or more path constraints that are easier
    -- for the Solver's to handle
    simplifyPC :: forall t . simplifier -> State t -> PathCond -> [PathCond]

    {-# INLINE simplifyPCs #-}
    -- | Simplifies the existing PathConds based on a new PathCond.
    simplifyPCs :: forall t. simplifier -> State t -> PathCond -> PathConds -> PathConds
    simplifyPCs _ _ _ = id
    
    {-# INLINE simplifyPCWithExprEnv #-}
    -- | Simplify the PathCond while also updating the ExprEnv
    simplifyPCWithExprEnv :: forall t . simplifier -> State t -> NameGen -> ExprEnv ->  PathCond -> (NameGen, ExprEnv, [PathCond])
    simplifyPCWithExprEnv simplifier s ng eenv pc =
        let pcs = simplifyPC simplifier s pc in (ng, eenv, pcs)

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification :: forall t . simplifier -> State t -> Bindings -> Model -> Model

-- | Combine two simplifiers
data (:>>) simp1 simp2 = simp1 :>> simp2

instance (Simplifier simp1, Simplifier simp2) => Simplifier (simp1 :>> simp2) where
    simplifyPC (simp1 :>> simp2) s = concatMap (simplifyPC simp2 s) . simplifyPC simp1 s

    simplifyPCs (simp1 :>> simp2) s pc = simplifyPCs simp2 s pc . simplifyPCs simp1 s pc

    simplifyPCWithExprEnv (simp1 :>> simp2) s ng eenv pc =
        let
            (ng', eenv', pc') = simplifyPCWithExprEnv simp2 s ng eenv pc
            ((ng'', eenv''), pc'') = L.mapAccumL (\(ng_, eenv_) pc_ ->
                                                    let (ng_', eenv_', pcs_) = simplifyPCWithExprEnv simp1 s ng_ eenv_ pc_ in ((ng_', eenv_'), pcs_)) (ng', eenv') pc'
        in 
        (ng'', eenv'', concat pc'')

    reverseSimplification (simp1 :>> simp2) s b m = reverseSimplification simp1 s b $ reverseSimplification simp2 s b m

data SomeSimplifier where
    SomeSimplifier :: forall simplifier
                    . Simplifier simplifier => simplifier -> SomeSimplifier

-- | A simplifier that does no simplification
data IdSimplifier = IdSimplifier

instance Simplifier IdSimplifier where
    simplifyPC _ _ pc = [pc]
    reverseSimplification _ _ _ m = m

-- | Tries to simplify based on simple arithmetic principles, i.e. x + 0 -> x
data ArithSimplifier = ArithSimplifier

instance Simplifier ArithSimplifier where
    simplifyPC _ _ pc = [modifyASTs simplifyArith pc]

    reverseSimplification _ _ _ m = m

simplifyArith :: Expr -> Expr
simplifyArith (App (App (Prim Plus _) e) l) | isZero l = e
simplifyArith (App (App (Prim Plus _) l) e) | isZero l = e

simplifyArith (App (App (Prim Mult _) _) l) | isZero l = l
simplifyArith (App (App (Prim Mult _) l) _) | isZero l = l

simplifyArith (App (App (Prim Minus _) e) l) | isZero l = e

-- 0 == lit * e is equivalent to 0 == e if lit /= 0
simplifyArith (App (App (Prim Eq t) l) (App (App (Prim Mult _) e1) e2))
    | isZero l
    , not (isZero e1)
    , isLit e1 = App (App (Prim Eq t) l) e2
    | isZero l
    , not (isZero e2)
    , isLit e2 = App (App (Prim Eq t) l) e1

-- 0 == - e is equivalent to 0 == e
simplifyArith (App (App (Prim Eq t) l) (App (Prim Negate _) e)) | isZero l = App (App (Prim Eq t) l) e

simplifyArith e = e

isZero :: Expr -> Bool
isZero (Lit (LitInt 0)) = True
isZero (Lit (LitRational 0)) = True
isZero _ = False

-- | Tries to simplify based on simple boolean principles, i.e. x == True -> x
data BoolSimplifier = BoolSimplifier

instance Simplifier BoolSimplifier where
    simplifyPC _ s pc = [modifyContainedASTs (simplifyBool (known_values s)) pc]

    reverseSimplification _ _ _ m = m

simplifyBool :: KnownValues -> Expr -> Expr
simplifyBool kv e
    | [Prim Eq _, Data (DataCon { dc_name = n }), e2 ] <- unApp e
    , n == dcTrue kv = e2
    | [Prim Eq _, e1, Data (DataCon { dc_name = n }) ] <- unApp e
    , n == dcTrue kv = e1
    | [Prim Eq _, Data (DataCon { dc_name = n }), e2 ] <- unApp e
    , n == dcFalse kv = mkNotExpr kv e2
    | [Prim Eq _, e1, Data (DataCon { dc_name = n }) ] <- unApp e
    , n == dcFalse kv = mkNotExpr kv e1
simplifyBool _ e = e

-- | Tries to simplify based on simple String principles, i.e. len x == 0 -> x == ""
-- (Note that rewrite 0 length constraints on Strings then composes well with the EqualitySimplifier.)
data StringSimplifier = StringSimplifier

instance Simplifier StringSimplifier where
    simplifyPC _ (State { known_values = kv, type_env = tenv }) pc =
                       [ modifyASTs (simplifyAllStrings kv tenv)
                       $ modifyContainedASTs simplifyString pc]

    reverseSimplification _ _ _ m = m

simplifyString :: Expr -> Expr
simplifyString e
    | [Prim Eq _, App (Prim StrLen t) v, Lit (LitInt 0) ] <- unApp e
    , TyFun (TyApp _ (TyCon (Name "Char" _ _ _) _)) _ <- t = mkApp [Prim Eq TyUnknown, v, Lit (LitString "")]
    | [Prim Eq _, Lit (LitInt 0), App (Prim StrLen t) v ] <- unApp e
    , TyFun (TyApp _ (TyCon (Name "Char" _ _ _) _)) _ <- t = mkApp [Prim Eq TyUnknown, v, Lit (LitString "")]
simplifyString e = e

simplifyAllStrings :: KnownValues -> TypeEnv -> Expr -> Expr
simplifyAllStrings kv tenv e
    | [Prim StrReplaceAll str_ra_ty, full, list, zs ] <- unApp e
    , [Data cons, _ {- type-}, _ {- head -}, App (Data emp) _] <- unApp list
    , dcName cons == dcCons kv
    , dcName emp == dcEmpty kv
    , Just (xs, ys) <- splitUpStrApp kv tenv full =
        mkApp [ Prim StrAppend TyUnknown
              , mkApp [Prim StrReplaceAll str_ra_ty, xs, list, zs ]
              , mkApp [Prim StrReplaceAll str_ra_ty, ys, list, zs ]
              ]
simplifyAllStrings _ _ e = e

splitUpStrApp :: KnownValues -> TypeEnv -> Expr -> Maybe (Expr, Expr)
splitUpStrApp _ _ e | [Prim StrAppend _, xs, ys] <- unApp e = Just (xs, ys)
splitUpStrApp kv tenv e | [Data cons, ty, x, xs] <- unApp e
                        , not $ isEmpty xs=
    Just (mkApp [Data cons, ty, x, App (mkEmpty kv tenv) ty], xs)
    where
        isEmpty (App (Data _) _) = True
        isEmpty _ = False
splitUpStrApp _ _ _ = Nothing

-- | Tries to simplify constraints involving checking if the value of an Int matches a concrete Float.
data FloatSimplifier = FloatSimplifier

instance Simplifier FloatSimplifier where
    -- Ints between -2^24 and 2^24 can be precisely represented as Floats.
    -- Ints between -2^53 and 2^53 can be precisely represented as Doubles.
    simplifyPC _ (State { known_values = kv, tyvar_env = tv })
                   (ExtCond (App (App (Prim FpEq _) (App (Prim IntToFloat _) v)) (Lit (LitFloat f))) b) | abs f <= 2 ^ (24 :: Integer) =
                        [ExtCond (mkEqExpr tv kv v (Lit (LitInt . toInteger $ fromEnum f))) b]

    simplifyPC _ (State { known_values = kv, tyvar_env = tv })
                   (ExtCond (App (App (Prim FpEq _) (App (Prim IntToDouble _) v)) (Lit (LitDouble d))) b) | abs d <= 2 ^ (53 :: Integer) =
                        [ExtCond (mkEqExpr tv kv v (Lit (LitInt . toInteger $ fromEnum d))) b]

    simplifyPC _ _ pc = [pc]

    reverseSimplification _ _ _ m = m


-- When we get a path constraint that is an equality between a variable and a small expression,
-- inline the small expression in all path constraints and in the ExprEnv.
data EqualitySimplifier = EqualitySimplifier

instance Simplifier EqualitySimplifier where
    simplifyPC _ s pc | Just _ <- smallEqPC (known_values s) pc = []
                      | otherwise = [pc]

    simplifyPCs _ s pc pcs | Just (n1, e@(Var (Id n2 _))) <- eq_pc = PC.mapPathCondsSCC n1 (replaceVar n1 e) (PC.join n1 n2 pcs)
                           | Just (n, e) <- eq_pc = PC.mapPathCondsSCC n (replaceVar n e) pcs
                           | otherwise = pcs
                           where
                            eq_pc = smallEqPC (known_values s) pc

    simplifyPCWithExprEnv _ s ng eenv pc
        | Just (n, e) <- smallEqPC (known_values s) pc =
            case e of
                Var (Id n' _) | n == n' -> (ng, eenv, [pc])
                _ -> (ng, E.insert n e eenv, [pc])
        | otherwise = (ng, eenv, [pc])
    
    reverseSimplification _ _ _ m = m

smallEqPC :: KnownValues
          -> PathCond
          -> Maybe (Name, Expr) -- ^ If PC is an equality between a variable and a constant, (Just (variable name, constant))
smallEqPC kv (ExtCond e True)
    | [Prim Eq _, e1, e2] <- es
    , Var (Id n _) <- e1
    , isSmall e2 = Just (n, e2)
    | [Prim Eq _, e1, e2] <- es
    , Var (Id n _) <- e2
    , isSmall e1 = Just (n, e1)
    | [Prim Eq _, Data (DataCon { dc_name = n }), e2] <- es
    , n == dcTrue kv = smallEqPC kv (ExtCond e2 True)
    | [Prim Eq _, e1, Data (DataCon { dc_name = n })] <- es
    , n == dcTrue kv = smallEqPC kv (ExtCond e1 True)
    where
        es = unApp e

        isSmall (Var _) = True
        isSmall (Data _) = True
        isSmall (Lit l) | nonMagicLit l = True
        isSmall _ = False

        -- String literals are "magic" because they are also data constructors.
        -- We need to ensure that all path conds/data constructors are lined up,
        -- and the equality solver risks messing this correspondence up.
        nonMagicLit (LitString _) = False
        nonMagicLit _ = True

smallEqPC kv (ExtCond (Var (Id n _)) True) = Just (n, mkTrue kv)
smallEqPC kv (ExtCond (Var (Id n _)) False) = Just (n, mkFalse kv)
smallEqPC _ (AltCond l (Var (Id n _)) True) = Just (n, Lit l)
smallEqPC _ _ = Nothing

-- Concretize symbolic literal wrappers. For example Char variables are converted to (C# c#) for some fresh c#
data LitConc = LitConc

instance Simplifier LitConc where
    simplifyPC _ _ pc = [pc]

    simplifyPCWithExprEnv _ (State { known_values = kv, type_env = tenv, tyvar_env = tv_env }) ng eenv pc =
        let
            -- Get all variables with types corresponding to literal wrappers
            cs = filter replacable_type $ varIds pc
            (cs', ng') = doRenames (map idName cs) ng cs
            conc_c = zip cs $ map toPrim cs'
            
            -- If a variable is NOT bound by a lambda, we want to reflect the concretization in the expression environment.
            lams = HS.map idName $ lamIds pc
            eenv' = foldr (\(Id nC t, nL) -> E.insert nC (concApprop t nL) . E.insertSymbolic nL) eenv (filter (\(Id n _, _) -> n `notElem` lams) conc_c)
            
            pc' = foldr (\(Id nC t, nL) -> modifyContainedASTs elimWrapper . replaceVarAndLam nC (concApprop t nL) nL) pc conc_c
        in
        (ng', eenv', [pc'])
        where
            replacable_type (Id _ t) =
                   t' == T.tyChar kv
                || t' == T.tyInt kv
                || t' == T.tyInteger kv
                || t' == T.tyWord kv
                || t' == T.tyFloat kv
                || t' == T.tyDouble kv
                where
                    t' = tyVarSubst tv_env t

            concApprop t i
                | t' == T.tyInt kv = concInt i
                | t' == T.tyInteger kv = concInteger i
                | t' == T.tyWord kv = concWord i
                | t' == T.tyFloat kv = concFloat i
                | t' == T.tyDouble kv = concDouble i
                | t' == T.tyChar kv = concChar i
                | otherwise = error $ "concApprop: impossible - unhandled type"
                where
                    t' = tyVarSubst tv_env t
            
            toPrim (Id n t)
                | t' == T.tyInt kv = Id n TyLitInt
                | t' == T.tyInteger kv = Id n TyLitInt
                | t' == T.tyWord kv = Id n TyLitWord
                | t' == T.tyFloat kv = Id n TyLitFloat
                | t' == T.tyDouble kv = Id n TyLitDouble
                | t' == T.tyChar kv = Id n TyLitChar
                | otherwise = error "concApprop: impossible - unhandled type"
                where
                    t' = tyVarSubst tv_env t

            concInt n = App (mkDCInt kv tenv) (Var n)
            concInteger n = App (mkDCInteger kv tenv) (Var n)
            concWord n = App (mkDCWord kv tenv) (Var n)
            concFloat n = App (mkDCFloat kv tenv) (Var n)
            concDouble n = App (mkDCDouble kv tenv) (Var n)
            concChar n = App (mkDCChar kv tenv) (Var n)

            elimWrapper (App (Data dc) e2)
                |  dcName dc == dcInt kv
                || dcName dc == dcInteger kv
                || dcName dc == dcWord kv
                || dcName dc == dcFloat kv
                || dcName dc == dcDouble kv
                || dcName dc == dcChar kv = e2
            elimWrapper e
                | Data dc:_ <- unApp e
                , dcName dc == dcCons kv = e
                | otherwise = modifyChildren elimWrapper e

    reverseSimplification _ _ _ m = m

replaceVarAndLam :: ASTContainer m Expr => Name -> Expr -> Id -> m -> m
replaceVarAndLam n e i = modifyASTs go
    where
        go v@(Var (Id n' _)) = if n == n' then e else v
        go (Lam lt (Id n' _) le) | n == n' = Lam lt i le
        go e' = e'

data LamVarSimplifier = LamVarSimplifier

instance Simplifier LamVarSimplifier where
    simplifyPC _ _ pc = [renameLamVars pc]

    reverseSimplification _ _ _ m = m

data ConstSimplifier = ConstSimplifier

instance Simplifier ConstSimplifier where
    simplifyPC _ _ (ExtCond e True) |
        [Prim Eq _, e1, e2] <- unApp e, e1 == e2 = []
    simplifyPC _ _ pc = [pc]
    reverseSimplification _ _ _ m = m

-- Rewrite functions with higher order arguments, like fold and map
data HigherOrderSimplifier = HigherOrderSimplifier

instance Simplifier HigherOrderSimplifier where
    simplifyPC _ _ pc = [pc]

    simplifyPCs _ _ pc = modifyASTs unfoldAppend . inFoldStringVars pc

    reverseSimplification _ _ _ m = m

unfoldAppend :: Expr -> Expr
-- Split up folds containg appends
unfoldAppend e | [Prim FoldLeft t, func, accum, App (App (Prim StrAppend t1) xs) ys] <- unApp e 
               , isSplittableFoldAppend func =
    mkApp [ Prim StrAppend t1
          , mkApp [Prim FoldLeft t, func, accum, xs]
          , mkApp [Prim FoldLeft t, func, accum, ys]
          ]
unfoldAppend e | [Prim FoldLeftI t, func, offset, accum, App (App (Prim StrAppend t1) xs) ys] <- unApp e
               , isSplittableFoldAppend func =
    mkApp [ Prim StrAppend t1
          , mkApp [Prim FoldLeftI t, func, offset, accum, xs]
          , mkApp [Prim FoldLeftI t, func, offset, accum, ys]
          ]

-- Split up folds containg ands
unfoldAppend e | [Prim FoldLeft t, func, accum, App (App (Prim StrAppend _) xs) ys] <- unApp e 
               , isSplittableFoldAnd func =
    mkApp [ Prim And TyUnknown
          , mkApp [Prim FoldLeft t, func, accum, xs]
          , mkApp [Prim FoldLeft t, func, accum, ys]
          ]
unfoldAppend e | [Prim FoldLeftI t, func, offset, accum, App (App (Prim StrAppend _) xs) ys] <- unApp e
               , isSplittableFoldAnd func =
    mkApp [ Prim And TyUnknown
          , mkApp [Prim FoldLeftI t, func, offset, accum, xs]
          , mkApp [Prim FoldLeftI t, func, offset, accum, ys]
          ]

-- Split up maps
unfoldAppend e | [Prim Map t, func, App (App (Prim StrAppend t1) xs) ys] <- unApp e =
    mkApp [ Prim StrAppend t1
          , mkApp [Prim Map t, func, xs]
          , mkApp [Prim Map t, func, ys]
          ]
unfoldAppend e | [Prim MapConcat t, func, App (App (Prim StrAppend t1) xs) ys] <- unApp e =
    mkApp [ Prim StrAppend t1
          , mkApp [Prim MapConcat t, func, xs]
          , mkApp [Prim MapConcat t, func, ys]
          ]

unfoldAppend e | [Prim MapConcatI t, func, App (App (Prim StrAppend t1) xs) ys] <- unApp e =
    mkApp [ Prim StrAppend t1
          , mkApp [Prim MapConcatI t, func, xs]
          , mkApp [Prim MapConcatI t, func, ys]
          ]
unfoldAppend e = e

-- foldl' (\zs x -> zs ++ f x) [] (xs ++ ys)
-- ==
-- foldl' (\zs x -> zs ++ f x) [] xs ++ foldl' (\zs x -> zs ++ f x) [] ys
isSplittableFoldAppend :: Expr -> Bool
isSplittableFoldAppend = isSplittableFold StrAppend

isSplittableFoldAnd :: Expr -> Bool
isSplittableFoldAnd = isSplittableFold And

isSplittableFold :: Primitive -> Expr -> Bool
isSplittableFold prim (Lam _ (Id col_v1 _) (Lam _ (Id _ _) e)) 
    | [Prim prim' _, Var (Id col_v2 _), e2] <- unApp e
    , prim == prim'
    , col_v1 == col_v2
    , col_v1 `notElem` varNames e2 = True
isSplittableFold _ _ = False

-- Looks for cases where a fold function is applied to a variable:
--  @ fold_left f i xs @
-- and that variable is defined as an equality:
--  @ xs = e1 ++ e2 @
-- Then inline the variable into the fold:
--  @ fold_left f i (e1 ++ e2) @
-- Not useful by itself, but allows opportunities for other optimizations 
inFoldStringVars :: PathCond -> PathConds -> PathConds
inFoldStringVars new_pc pcs
    -- If we get a new mapping of a variable to a string/sequence
    | Just (n1, e@(Var (Id n2 _))) <- eq_pc = PC.mapPathCondsSCC n1 (replaceVarFold n1 e) (PC.join n1 n2 pcs)
    | Just (n, e) <- eq_pc = PC.mapPathCondsSCC n (replaceVarFold n e) pcs
    -- If we get a new fold of a string/sequence
    | Just (Id init_n _) <- isFold new_pc
    , e:_ <- PC.mapMaybePathCondsSCC init_n (specEqPC init_n) pcs = replaceVar init_n e pcs
    where
        eq_pc = eqPC new_pc
inFoldStringVars _ pcs = pcs

specEqPC :: Name -> PathCond -> Maybe Expr
specEqPC n pc =
    case eqPC pc of
        Just (n1, e) | n == n1 -> Just e
        _ -> Nothing

eqPC :: PathCond
     -> Maybe (Name, Expr) -- ^ If PC is an equality between a variable and a value
eqPC (ExtCond e True)
    | [Prim Eq _, e1, e2] <- es
    , Var (Id n _) <- e1  = Just (n, e2)
    | [Prim Eq _, e1, e2] <- es
    , Var (Id n _) <- e2  = Just (n, e1)
    where
        es = unApp e
eqPC _ = Nothing

isFold :: PathCond -> Maybe Id
isFold (ExtCond e _)
    | [(Prim prim _), _, (Var init_i), _] <- unApp e
    , prim == FoldLeft || prim == FoldLeftI || prim == MapConcat = Just init_i
isFold _ = Nothing

replaceVarFold :: ASTContainer m Expr => Name -> Expr -> m -> m
replaceVarFold n e = modifyContainedASTs (replaceVarFold' n e)

replaceVarFold' :: Name -> Expr -> Expr -> Expr
replaceVarFold' n e e2
    | [prim_fold@(Prim prim _), f, init_e, (Var (Id lst_n _))] <- unApp e2
    , lst_n == n
    , prim == FoldLeft || prim == FoldLeftI || prim == MapConcat =
        mkApp [ prim_fold, f, init_e, e]
replaceVarFold' n _ le@(Lam _ (Id n' _) _) | n == n' = le
replaceVarFold' n e (Case b i@(Id n' _) t as) | n == n' = Case (replaceVarFold n e b) i t as
replaceVarFold' n e (Case b i t as) = Case (replaceVarFold' n e b) i t (map repAlt as)
    where
        repAlt a@(Alt (DataAlt _ is) _)
            | n `elem` map idName is = a
        repAlt a = modifyContainedASTs (replaceVarFold' n e) a
replaceVarFold' n _ le@(Let b _) | n `elem` map (idName . fst) b = le
replaceVarFold' n e e' = modifyChildren (replaceVarFold' n e) e'


