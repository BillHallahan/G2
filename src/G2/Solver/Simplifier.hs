{-# LANGUAGE FlexibleContexts, GADTs, RankNTypes, OverloadedStrings, TypeOperators, ViewPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , SomeSimplifier (..)
                            , (:>>) (..)
                            , (.>>)
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

                            , mkSeqNth
                            ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues as KV
import G2.Language.Monad
import qualified G2.Language.Monad.ExprEnv as E
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Typing as T

import qualified Control.Monad.State.Lazy as SM

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
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

(.>>) :: SomeSimplifier -> SomeSimplifier -> SomeSimplifier
SomeSimplifier s1 .>> SomeSimplifier s2 = SomeSimplifier (s1 :>> s2)

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
    simplifyPC _ s (ExtCond e False) =
        [modifyContainedASTs (simplifyBool (known_values s)) (ExtCond (App (Prim Not TyUnknown) e) True)]
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
    | (App (Prim Not _) (App (Prim Not _) e')) <- e = e'
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

    -- | [Prim Eq _, e1, e2] <- unApp e
    -- , [Prim StrIndexOf _, xs, ys, Lit (LitInt 0)] <- unApp e1
    -- , Lit (LitInt (- 1)) <- e2 = App (Prim Not TyUnknown) $ mkApp [ Prim StrContains TyUnknown, xs, ys]

simplifyAllStrings _ _ e = e

splitUpStrApp :: KnownValues -> TypeEnv -> Expr -> Maybe (Expr, Expr)
splitUpStrApp _ _ e | [Prim StrAppend _, xs, ys] <- unApp e = Just (xs, ys)
splitUpStrApp kv tenv e | [Data cons, ty, x, xs] <- unApp e
                        , not $ isEmpty kv xs =
    Just (mkApp [Data cons, ty, x, App (mkEmpty kv tenv) ty], xs)
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
                Var (Id n' _) | n == n' -> (ng, eenv, [])
                _ -> (ng, E.insert n e eenv, [])
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
            eenv' = foldr (\(Id nC t, nL) -> E.alter (concAppropEEnv t (Var nL)) nC . E.insertSymbolic nL) eenv (filter (\(Id n _, _) -> n `notElem` lams) conc_c)
            
            pc' = foldr (\(Id nC t, nL) -> replaceVarAndLam nC (concApprop t (Var nL)) nL) pc conc_c
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

            concAppropEEnv _ _ (Just (E.ExprObj e)) = Just . E.ExprObj $ e
            concAppropEEnv t e _ = Just . E.ExprObj $ concApprop t e

            concApprop t e
                | t' == T.tyInt kv = concInt e
                | t' == T.tyInteger kv = concInteger e
                | t' == T.tyWord kv = concWord e
                | t' == T.tyFloat kv = concFloat e
                | t' == T.tyDouble kv = concDouble e
                | t' == T.tyChar kv = concChar e
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

            concInt e = App (mkDCInt kv tenv) e
            concInteger e = App (mkDCInteger kv tenv) e
            concWord e = App (mkDCWord kv tenv) e
            concFloat e = App (mkDCFloat kv tenv) e
            concDouble e = App (mkDCDouble kv tenv) e
            concChar e = App (mkDCChar kv tenv) e
    
    simplifyPCs _ (State { known_values = kv, expr_env = eenv }) _ = modifyContainedASTs (elimWrapper kv eenv)

    reverseSimplification _ _ _ m = m

elimWrapper :: KnownValues -> ExprEnv -> Expr -> Expr
elimWrapper kv eenv = go
    where
        go (App (Data dc) e2) | elimName $ dc_name dc = modifyChildren go e2
        go(App (Prim (Selector dc _) _) e2) | elimName $ dc_name dc = modifyChildren go e2
        go (App (Prim (IsConstructor dc) _) _) | elimName $ dc_name dc = mkTrue kv
        go v@(Var (Id n _))
            | Just (E.Conc e_) <- E.deepLookupConcOrSym n eenv =
                case appCenter e_ of
                    Data dc | isPrimWrapperDC kv dc -> go e_
                            | otherwise -> v
                    _ -> go e_
        go e
            -- | Data dc:_ <- unApp e
            -- , dcName dc == dcCons kv = e
            | otherwise = modifyChildren go e

        elimName n =
                n == dcInt kv
            || n == dcInteger kv
            || n == dcWord kv
            || n == dcFloat kv
            || n == dcDouble kv
            || n == dcChar kv

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

    simplifyPCs _ (State { type_env = tenv, known_values = kv }) pc =
        modifyASTs (simplifyUnitMap kv) . splitAnds . modifyASTs (unfoldAppend tenv kv) . inFoldStringVars pc . modifyASTs lenOfMap

    simplifyPCWithExprEnv _ s@(State { known_values = kv, tyvar_env = tv_env }) ng eenv pc =
        let 
            (pcs', eenv', ng') = indexOfToAppended (s { expr_env = eenv }) ng pc
            pcs'' = map (seqNthMap kv tv_env . fuseFoldLeftMap . notContainsToFoldMap kv tv_env) pcs'
            ((s', ng''), pcs''') = L.mapAccumL
                                        (\(s_, ng_) pc_ -> let (pc_', eenv_, ng_') = mapContainsUnit (s { expr_env = eenv }) ng_ pc_ in
                                                            ((s_ { expr_env = eenv_ }, ng_'), pc_'))
                                        (s { expr_env = eenv' }, ng')
                                        pcs''
            pcs4 = simplifyLams $ concat pcs'''
        in
        (ng'', expr_env s', pcs4)

    reverseSimplification _ _ _ m = m

lenOfMap :: Expr -> Expr
lenOfMap e
    | [Prim StrLen _, e'] <- unApp e
    , [Prim Map _, _, e''] <- unApp e' = mkApp [Prim StrLen TyUnknown, e'']
lenOfMap e = e

unfoldAppend :: TypeEnv -> KnownValues -> Expr -> Expr
-- Split up folds containg appends
unfoldAppend tenv kv e | [Prim FoldLeft t, func, accum, poss_app] <- unApp e
                       , Just (xs, ys) <- appendedSeqs tenv kv poss_app
                       , Just (pr, init_e) <- isSplittableFold tenv kv func =
    mkApp [ pr
          , mkApp [Prim FoldLeft t, func, accum, xs]
          , mkApp [Prim FoldLeft t, func, init_e, ys]
          ]
unfoldAppend tenv kv e | [Prim FoldLeft t, func, accum, poss_app] <- unApp e
                       , Just (xs, ys) <- appendedSeqs tenv kv poss_app
                       , Just (pr, init_e) <- isSplittableFoldRev tenv kv func =
    mkApp [ pr
          , mkApp [Prim FoldLeft t, func, init_e, ys]
          , mkApp [Prim FoldLeft t, func, accum, xs]
          ]
-- unfoldAppend tenv kv e | [Prim FoldLeftI t, func, offset, accum, poss_app] <- unApp e
--                        , isEmpty kv accum
--                        , Just (xs, ys) <- appendedSeqs tenv kv poss_app
--                        , isSplittableFoldAppend tenv kv func =
--     mkApp [ Prim StrAppend TyUnknown
--           , mkApp [Prim FoldLeftI t, func, offset, accum, xs]
--           , mkApp [Prim FoldLeftI t, func, offset, accum, ys]
--           ]

-- Split up maps
unfoldAppend tenv kv e | [Prim Map t, func, poss_app] <- unApp e
                       , Just (xs, ys) <- appendedSeqs tenv kv poss_app =
    mkApp [ Prim StrAppend TyUnknown
          , mkApp [Prim Map t, func, xs]
          , mkApp [Prim Map t, func, ys]
          ]
unfoldAppend tenv kv e | [Prim MapConcat t, func, poss_app] <- unApp e
                       , Just (xs, ys) <- appendedSeqs tenv kv poss_app =
    mkApp [ Prim StrAppend TyUnknown
          , mkApp [Prim MapConcat t, func, xs]
          , mkApp [Prim MapConcat t, func, ys]
          ]

unfoldAppend tenv kv e | [Prim MapConcatI t, func, poss_app] <- unApp e
                       , Just (xs, ys) <- appendedSeqs tenv kv poss_app =
    mkApp [ Prim StrAppend TyUnknown
          , mkApp [Prim MapConcatI t, func, xs]
          , mkApp [Prim MapConcatI t, func, ys]
          ]
unfoldAppend _ _ e = e

appendedSeqs :: TypeEnv -> KnownValues -> Expr -> Maybe (Expr, Expr)
appendedSeqs tenv kv (consToAppend tenv kv -> (App (App (Prim StrAppend _) xs) ys)) = Just (xs, ys)
appendedSeqs _ _ _ = Nothing

-- | Convert (x:xs) into ([x] ++ xs) so that other simplifications fire
consToAppend :: TypeEnv -> KnownValues -> Expr -> Expr
consToAppend _ kv e@(App (App (App (Data dc) _) _) (App (Data dc_emp) _)) -- Make sure we don't go into an infinite loop
    | dc_name dc == dcCons kv
    , dc_name dc_emp == dcEmpty kv = e
consToAppend tenv kv (App (App (App (Data dc) (Type t)) x) ys) | dc_name dc == dcCons kv =
    let xs = mkG2List kv tenv t [x] in
    mkApp [Prim StrAppend TyUnknown, xs, ys]
consToAppend _ _ e = e

-- The identity function can be split, as long as we eventually find a Prim
-- Note that types don't need to match here, since the type checker does that
-- for us
data PrimMatch = SpecificPrim Expr Expr | AnyPrim
    deriving (Eq, Show)

-- foldl' (\zs x -> zs ++ f x) [] (xs ++ ys)
-- ==
-- foldl' (\zs x -> zs ++ f x) [] xs ++ foldl' (\zs x -> zs ++ f x) [] ys
-- OR
-- foldl' (\zs x -> if f x then zs ++ [x] else xs) [] (xs ++ ys)
-- ==
-- foldl' (\zs x -> if f x then zs ++ [x] else zs) [] xs
--     ++ foldl' (\zs x -> f x then zs ++ [x] else zs) [] ys
-- ... and so on. Note that this can generalize to any monoid!
isSplittableFold :: TypeEnv -> KnownValues -> Expr -> Maybe (Expr, Expr)
isSplittableFold tenv kv f =
    case isSplittableFold' tenv kv (modifyASTs (consToAppend tenv kv) f) of
        Just (SpecificPrim pr e) -> Just (pr, e)
        _ -> Nothing

isSplittableFold' :: TypeEnv
                  -> KnownValues
                  -> Expr -- ^ Function being folded over
                  -> Maybe PrimMatch
isSplittableFold' tenv kv (Lam _ (Id col_v1 _) (Lam _ (Id _ _) e)) = checkBody e
    where
        checkBody body
            | [pr@(Prim prim _), Var (Id col_v2 t), e2] <- unApp $ makeRightAssoc body
            , Just ident_e <- HM.lookup prim (assocPrimToIdent tenv kv t)
            , col_v1 == col_v2
            , col_v1 `notElem` varNames e2 = Just $ SpecificPrim pr ident_e

            | Var (Id col_v2 _) <- body
            , col_v1 == col_v2 = Just AnyPrim

            | [Prim Ite _, cond, tb, fb] <- unApp body
            , col_v1 `notElem` varNames cond
            , Just tb1 <- checkBody tb
            , Just fb1 <- checkBody fb = resolveBranches tb1 fb1

            | otherwise = Nothing
isSplittableFold' _ _ _ = Nothing

resolveBranches :: PrimMatch -> PrimMatch -> Maybe PrimMatch
resolveBranches t@(SpecificPrim p1 e1) (SpecificPrim p2 e2) | p1 == p2 && e1 == e2 = Just t
resolveBranches t@(SpecificPrim _ _) AnyPrim = Just t
resolveBranches AnyPrim f@(SpecificPrim _ _) = Just f
resolveBranches AnyPrim AnyPrim = Just AnyPrim
resolveBranches _ _ = Nothing

assocPrimToIdent :: TypeEnv -> KnownValues -> Type -> HM.HashMap Primitive Expr
assocPrimToIdent tenv kv t =
    let t' = case t of TyApp _ t_ -> t_; _ -> t in
    HM.fromList [ (StrAppend, App (mkEmpty kv tenv) (Type t'))
                , (And, mkTrue kv)
                , (Or, mkFalse kv)
    
                , (Plus, Lit $ LitInt 0)
                , (Mult, Lit $ LitInt 1) ]

isEmpty :: KnownValues -> Expr -> Bool
isEmpty kv (App (Data dc) _) = dc_name dc == dcEmpty kv
isEmpty _ _ = False

-- | Convert applications to be right associative
makeRightAssoc :: Expr -> Expr
makeRightAssoc
    (App 
        (App
            (Prim prim1 t1)
            (App (App (Prim prim2 _) e1) e2)
        )
    e3) | isAssoc prim1 , prim1 == prim2 =
        makeRightAssoc $ App
            (App (Prim prim1 t1) e1)
            (App (App (Prim prim1 t1) e2) e3)
makeRightAssoc e = e

isAssoc :: Primitive -> Bool
isAssoc StrAppend = True
isAssoc And = True
isAssoc Or = True
isAssoc Plus = True
isAssoc Mult = True
isAssoc _ = False -- Conservative assumption

-- foldl' (\zs x -> f x:zs) [] (xs ++ ys)
-- ==
-- foldl' (\zs x -> f x:zs) [] ys ++ foldl' (\zs x -> f x:zs) [] xs
isSplittableFoldRev :: TypeEnv -> KnownValues -> Expr -> Maybe (Expr, Expr)
isSplittableFoldRev tenv kv f =
    case isSplittableFoldRev' tenv kv (modifyASTs (consToAppend tenv kv) f) of
        Just (SpecificPrim pr e) -> Just (pr, e)
        _ -> Nothing

isSplittableFoldRev' :: TypeEnv
                  -> KnownValues
                  -> Expr -- ^ Function being folded over
                  -> Maybe PrimMatch
isSplittableFoldRev' tenv kv (Lam _ (Id col_v1 _) (Lam _ (Id _ _) e)) = checkBody e
    where
        checkBody body
            | [pr@(Prim prim _), e1, Var (Id col_v2 t)] <- unApp $ makeRightAssoc body
            , Just ident_e <- HM.lookup prim (assocPrimToIdent tenv kv t)
            , col_v1 == col_v2
            , col_v1 `notElem` varNames e1 = Just $ SpecificPrim pr ident_e

            | Var (Id col_v2 _) <- body
            , col_v1 == col_v2 = Just AnyPrim

            | [Prim Ite _, cond, tb, fb] <- unApp body
            , col_v1 `notElem` varNames cond
            , Just tb1 <- checkBody tb
            , Just fb1 <- checkBody fb = resolveBranches tb1 fb1

            | otherwise = Nothing
isSplittableFoldRev' _ _ _ = Nothing

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


seqNthMap :: KnownValues -> TyVarEnv -> PathCond -> PathCond
seqNthMap kv tv_env = modifyASTs go
    where
        go e
            | [Prim SeqNth _, e1, e2] <- unApp e
            , [Prim Map _, f, lst] <- unApp e1 =
                App
                  f
                $ mkSeqNth kv tv_env lst e2
            | otherwise = e

mapContainsUnit :: State t -> NameGen -> PathCond -> ([PathCond], ExprEnv, NameGen)
mapContainsUnit s@(State { known_values = kv, tyvar_env = tv_env }) ng pc = 
    let ((pc', (s', ng')), extra_pc) = SM.runState (runStateNGT (go pc) s ng) [] in
    (pc':extra_pc, expr_env s', ng')
    where
        -- Rewrite
        --    (contains (seq.map f lst) [x])
        -- to
        --    (f (lst !! i) == [x])
        go :: SM.MonadState [PathCond] m => PathCond -> StateNGT t m PathCond
        go (ExtCond e True)
            | [Prim StrContains _, map_e, unit_e] <- unApp e
            , [Prim Map _, f, lst] <- unApp map_e
            , Just unit_v <- getUnit kv unit_e = do
                elem_ind <- freshIdN TyLitInt
                E.insertSymbolicE elem_ind
                let gt_0 = ExtCond (mkApp [Prim Le TyUnknown, Lit (LitInt 0), Var elem_ind]) True
                    lt_len = ExtCond (mkApp [Prim Lt TyUnknown, Var elem_ind, App (Prim StrLen TyUnknown) lst]) True
                    
                    index_lst_and_app = App f $ mkSeqNth kv tv_env lst (Var elem_ind)

                SM.lift $ SM.modify (\xs -> gt_0:lt_len:xs)

                return $ ExtCond (mkApp [Prim Eq TyUnknown, index_lst_and_app, unit_v]) True
        go pc_ = return pc_

notContainsToFoldMap :: KnownValues
                     -> TyVarEnv
                     -> PathCond
                     -> PathCond
notContainsToFoldMap kv tv_env (ExtCond (App (Prim Not _) e) True)
    | [Prim StrContains _, map_e, unit_e] <- unApp e
    , [Prim Map _, _, _] <- unApp map_e
    , Just unit_v <- getUnit kv unit_e = ExtCond (notContainsValToFold kv tv_env map_e unit_v) True
notContainsToFoldMap _ _ e = e

notContainsValToFold :: KnownValues
                     -> TyVarEnv
                     -> Expr -- ^ List being checked
                     -> Expr -- ^ Value being checked for 
                     -> Expr
notContainsValToFold kv tv_env lst v =
    let
        accum_id = Id (Name "G2_!!_LAM_Acc" Nothing 0 Nothing) (T.tyBool kv)
        e_id = Id (Name "G2_!!_LAM_Val" Nothing 0 Nothing) (typeOf tv_env v)

        f = Lam TermL accum_id
          . Lam TermL e_id
          $ mkApp [ Prim And TyUnknown
                  , Var accum_id
                  , mkApp [ Prim Neq TyUnknown, Var e_id, v]
                  ]
    in
    mkApp [ Prim FoldLeft TyUnknown
          , f
          , mkTrue kv
          , lst]

getUnit :: KnownValues -> Expr -> Maybe Expr
getUnit kv (App 
                (App 
                    (App (Data dc_cons) _)
                    x
                ) 
                (App (Data dc_emp) _)
            )
    | dc_name dc_cons == dcCons kv
    , dc_name dc_emp == dcEmpty kv = Just x
getUnit _ (App (Prim SeqUnit _) e) = Just e
getUnit _ _ = Nothing

indexOfToAppended :: State t -> NameGen -> PathCond -> ([PathCond], ExprEnv, NameGen)
indexOfToAppended s@(State { known_values = kv, tyvar_env = tv_env }) ng pc = 
    let ((pc', (s', ng')), extra_pc) = SM.runState (runStateNGT (go pc) s ng) [] in
    (pc':extra_pc, expr_env s', ng')
    where
        -- Rewrite
        --    (seq.indexof (seq.map f lst) [e]) == n
        -- to
        --    seq.prefixof lst xs
        --    length xs == n
        --    not (contains (seq.map f xs) [e])
        --    f (seq.nth lst n) == e
        go :: SM.MonadState [PathCond] m => PathCond -> StateNGT t m PathCond
        go (ExtCond e True)
            | [Prim Eq _, check_ind, exp_ind] <- unApp e
            , isNotNeg exp_ind
            , [Prim StrIndexOf _, map_e, unit_e, Lit (LitInt 0)] <- unApp check_ind
            , [Prim Map _, f, lst] <- unApp map_e
            , Just unit_v <- getUnit kv unit_e = do
                let list_ty = typeOf tv_env lst
                start_i <- freshIdN list_ty
                end_i <- freshIdN list_ty
                insertSymbolicE start_i
                insertSymbolicE end_i
                

                let prefix_of = ExtCond
                                   (mkApp [ Prim Eq TyUnknown
                                          , lst
                                          , mkApp [Prim StrAppend TyUnknown, Var start_i, Var end_i]
                                          ]
                                   )
                                   True

                    start_len_cond = ExtCond
                                     (mkApp [ Prim Eq TyUnknown
                                            , mkApp [Prim StrLen TyUnknown, Var start_i]
                                            , exp_ind
                                            ])
                                     True
                    end_len_cond = ExtCond
                                     (mkApp [ Prim Gt TyUnknown
                                            , mkApp [Prim StrLen TyUnknown, Var end_i]
                                            , Lit (LitInt 0)
                                            ])
                                     True
                    not_contains_start = ExtCond
                                            ( App (Prim Not TyUnknown)
                                            $ mkApp [ Prim StrContains TyUnknown
                                                    , mkApp [ Prim Map TyUnknown, f, Var start_i]
                                                    , unit_e ]
                                            )
                                            True
                    elem_maps_to = ExtCond
                                        (mkApp
                                            [ Prim Eq TyUnknown
                                            , unit_v
                                            , App f $ mkSeqNth kv tv_env (Var end_i) (Lit $ LitInt 0) ]
                                        )
                                        True

                SM.lift $ SM.modify (\xs -> start_len_cond:end_len_cond:not_contains_start:elem_maps_to:xs)

                return prefix_of
        go pc_ = return pc_

        isNotNeg (Lit (LitInt x)) = x >= 0
        isNotNeg (App (Prim StrLen _) _) = True
        isNotNeg _ = False

fuseFoldLeftMap :: PathCond -> PathCond
fuseFoldLeftMap = modifyASTs go
    where
        go e
            | [Prim FoldLeft _, fold_f, v, fold_lst] <- unApp e
            , [Prim Map _, map_f, map_lst] <- unApp fold_lst
            , Lam acc_term acc_i (Lam val_term val_i fold_e) <- fold_f
            , (Lam _ (Id _ map_t) _) <- map_f =
                let
                    new_val_i = Id (idName val_i) map_t
                    mapped_val_i = App map_f $ Var new_val_i
                    fold_f' = Lam acc_term acc_i
                            . Lam val_term new_val_i
                            $ replaceVar (idName val_i) mapped_val_i fold_e
                in
                mkApp [ Prim FoldLeft TyUnknown
                    , fold_f'
                    , v
                    , map_lst]
        go e = e

splitAnds :: PathConds -> PathConds
splitAnds = PC.concatMapHashedPCs go
    where go pc
            | ExtCond e True <- PC.unhashedPC pc
            , [Prim And _, e1, e2] <- unApp e = [ PC.hashedPC $ ExtCond e1 True
                                                , PC.hashedPC $ ExtCond e2 True ]
            | otherwise = [pc]

mkSeqNth :: KnownValues -> TyVarEnv -> Expr -> Expr -> Expr
mkSeqNth kv tv_env lst ind =
    let
        t_lst = typeOf tv_env lst
        t = TyFun t_lst (TyFun TyLitInt (G2.Language.tyBool kv))

        -- Seq.nth returns a unicode character when applied to a String, so have to wrap in a SeqUnit to compare
        -- to strings
        wrap = case t_lst of
                    TyApp _ (TyCon n _) | n == KV.tyChar kv -> \e -> mkApp [Prim SeqUnit TyUnknown, e]
                    TyLitChar -> \e -> mkApp [Prim SeqUnit TyUnknown, e]
                    _ -> id
    in
    wrap $ mkApp [Prim SeqNth t, lst, ind]

simplifyUnitMap :: KnownValues -> Expr -> Expr
simplifyUnitMap kv e
    | [Prim Map _, f, e1] <- unApp e
    , Just unit_v <- getUnit kv e1 = App (Prim SeqUnit TyUnknown) (App f unit_v)
    | otherwise = e