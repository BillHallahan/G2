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
                            , CharConc (..)) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Typing as T
import Debug.Trace

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
    simplifyPCWithExprEnv :: forall t . simplifier -> State t -> NameGen -> ExprEnv ->  PathCond -> (NameGen, ExprEnv, PathCond)
    simplifyPCWithExprEnv _ _ ng eenv pc = (ng, eenv, pc)

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
        in 
        simplifyPCWithExprEnv simp1 s ng' eenv' pc'

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
    -- Remove unneeded length calls to the solver
    -- length ("abcdef" ++ x) -> length "abcdef" ++ length x -> 6 + length x 
    | [Prim StrLen slt, App (App (Prim StrAppend _) conc_str) var_str] <- unApp e, isConcStr conc_str = 
        mkApp [Prim Plus TyUnknown, Lit (LitInt $ concStrLen conc_str), App (Prim StrLen slt) var_str]
    | [Prim StrLen slt, App (App (Prim StrAppend _) var_str) conc_str] <- unApp e, isConcStr conc_str = 
        mkApp [Prim Plus TyUnknown, Lit (LitInt $ concStrLen conc_str), App (Prim StrLen slt) var_str]
    where
        isConcStr (App (Data _) _) = True
        isConcStr (App (App (App (Data _) _) _) _) = True
        isConcStr _ = False

        concStrLen (App (Data _) _) = 0
        concStrLen (App (App (App (Data _) _) _) str_tail) = 1 + concStrLen str_tail
        concStrLen e = error $ "expr is not a concrete string:\n" ++ show e
simplifyString e = e
--  simplifyString e = trace (show (unApp e) ++ "\n") e

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

    simplifyPCWithExprEnv _ s ng eenv pc
        | Just (n, e) <- smallEqPC (known_values s) pc =
            case e of
                Var (Id n' _) | n == n' -> (ng, eenv, pc)
                _ -> (ng, E.insert n e eenv, pc)
        | otherwise = (ng, eenv, pc)
    
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

-- Concretize symbolic Char variables to be (C# c#) for some fresh c#
data CharConc = CharConc

instance Simplifier CharConc where
    simplifyPC _ _ pc = [pc]

    simplifyPCWithExprEnv _ s@(State { known_values = kv, type_env = tenv }) ng eenv pc =
        let
            cs = map idName . filter (\(Id _ t) -> t == T.tyChar kv) $ varIds pc
            (cs', ng') = renameAll cs ng
            conc_c = zip cs $ map (flip Id TyLitChar) cs'
            eenv' = foldr (\(nC, nL) -> E.insert nC (concChar nL) . E.insertSymbolic nL) eenv conc_c
            pc' = foldr (\(nC, nL) -> replaceVar nC (concChar nL)) pc conc_c
        in
        (ng', eenv', pc')
        where
            dc_char = mkDCChar kv tenv
            concChar n = App dc_char (Var n)

    reverseSimplification _ _ _ m = m
