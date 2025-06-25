{-# LANGUAGE RankNTypes, OverloadedStrings, TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , (:>>) (..)
                            , IdSimplifier (..)
                            , ArithSimplifier (..)
                            , BoolSimplifier (..)
                            , StringSimplifier (..)
                            , FloatSimplifier (..)
                            , EqualitySimplifier (..)
                            , ConstSimplifier (..)) where

import G2.Execution.PrimitiveEval
import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import qualified G2.Language.PathConds as PC
import Debug.Trace

class Simplifier simplifier where
    -- | Simplifies a PC, by converting it into one or more path constraints that are easier
    -- for the Solver's to handle
    simplifyPC :: forall t . simplifier -> State t -> PathCond -> [PathCond]

    {-# INLINE simplifyPCs #-}
    -- | Simplifies the existing PathConds based on a new PathCond.
    simplifyPCs :: forall t. simplifier -> State t -> PathCond -> PathConds -> PathConds
    simplifyPCs _ _ _ = id
    
    {-# INLINE updateExprEnvPC #-}
    -- | Update the ExprEnv based on a new PathCond
    updateExprEnvPC :: forall t . simplifier -> State t -> PathCond -> ExprEnv -> ExprEnv
    updateExprEnvPC _ _ _ = id

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification :: forall t . simplifier -> State t -> Bindings -> Model -> Model

-- | Combine two simplifiers
data (:>>) simp1 simp2 = simp1 :>> simp2

instance (Simplifier simp1, Simplifier simp2) => Simplifier (simp1 :>> simp2) where
    simplifyPC (simp1 :>> simp2) s = concatMap (simplifyPC simp2 s) . simplifyPC simp1 s

    simplifyPCs (simp1 :>> simp2) s pc = simplifyPCs simp2 s pc . simplifyPCs simp1 s pc

    updateExprEnvPC (simp1 :>> simp2) s pc = updateExprEnvPC simp2 s pc . updateExprEnvPC simp1 s pc

    reverseSimplification (simp1 :>> simp2) s b m = reverseSimplification simp1 s b $ reverseSimplification simp2 s b m

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

-- | Tries to simplify literal expressions, i.e. 1 == 1 -> True
data ConstSimplifier = ConstSimplifier

instance Simplifier ConstSimplifier where 
    simplifyPC _ _ pc = [pc]
    simplifyPCs _ s _ = PC.map (evalPrims (type_env s) (known_values s))
        

    reverseSimplification _ _ _ m = m

-- areLiteralsEq :: Expr -> Expr -> Maybe Bool
-- areLiteralsEq (Lit l) (Lit r) = Just (l == r)
-- areLiteralsEq _ _ = Nothing

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
    simplifyPC _ _ pc = [modifyContainedASTs simplifyString pc]

    reverseSimplification _ _ _ m = m

simplifyString :: Expr -> Expr
simplifyString e
    | [Prim Eq _, App (Prim StrLen _) v, Lit (LitInt 0) ] <- unApp e = mkApp [Prim Eq TyUnknown, v, Lit (LitString "")]
    | [Prim Eq _, Lit (LitInt 0), App (Prim StrLen _) v ] <- unApp e = mkApp [Prim Eq TyUnknown, v, Lit (LitString "")]
simplifyString e = e

-- | Tries to simplify constraints involving checking if the value of an Int matches a concrete Float.
data FloatSimplifier = FloatSimplifier

instance Simplifier FloatSimplifier where
    -- Ints between -2^24 and 2^24 can be precisely represented as Floats.
    -- Ints between -2^53 and 2^53 can be precisely represented as Doubles.
    simplifyPC _ (State { known_values = kv })
                   (ExtCond (App (App (Prim FpEq _) (App (Prim IntToFloat _) v)) (Lit (LitFloat f))) b) | abs f <= 2 ^ (24 :: Integer) =
                        [ExtCond (mkEqExpr kv v (Lit (LitInt . toInteger $ fromEnum f))) b]

    simplifyPC _ (State { known_values = kv })
                   (ExtCond (App (App (Prim FpEq _) (App (Prim IntToDouble _) v)) (Lit (LitDouble d))) b) | abs d <= 2 ^ (53 :: Integer) =
                        [ExtCond (mkEqExpr kv v (Lit (LitInt . toInteger $ fromEnum d))) b]

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

    updateExprEnvPC _ s pc eenv
        | Just (n, e) <- smallEqPC (known_values s) pc =
            case e of
                Var (Id n' _) | n == n' -> eenv
                _ -> E.insert n e eenv
        | otherwise = eenv
    
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