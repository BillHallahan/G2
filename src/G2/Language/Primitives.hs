{-# LANGUAGE OverloadedStrings #-}

module G2.Language.Primitives ( primStr
                              , strToPrim
                              , mkGe
                              , mkGt
                              , mkEq
                              , mkNeq
                              , mkLt
                              , mkLe
                              , mkAnd
                              , mkOr
                              , mkNot
                              , mkPlus
                              , mkMinus
                              , mkMult
                              , mkDiv
                              , mkMod
                              , mkNegate
                              , mkImplies
                              , mkIff
                              , mkFromInteger
                              , mkToInteger
                              , mkEqPrimInt
                              , mkEqPrimFloat
                              , mkEqPrimDouble
                              , mkEqPrimChar
                              , mkAndPrim
                              , mkGePrimInt
                              , mkLePrimInt) where

import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues as KV
import G2.Language.Syntax
import G2.Language.Typing

import Data.Foldable
import qualified Data.Text as T

primStr :: Primitive -> T.Text
primStr Ge = ">="
primStr Gt = ">"
primStr Eq = "=="
primStr Neq = "/="
primStr Lt = "<"
primStr Le = "<="
primStr And = "&&"
primStr Or = "||"
primStr Not = "not"
primStr Implies = "implies"
primStr Iff = "iff"
primStr Plus = "+"
primStr Minus = "-"
primStr Mult = "*"
primStr Div = "/"
primStr DivInt = "/"
primStr Quot = "quot"
primStr Mod = "mod"
primStr Negate = "negate"
primStr SqRt = "sqrt"
primStr IntToFloat = "fromIntegral"
primStr IntToDouble = "fromIntegral"
primStr RationalToDouble = "rationalToDouble"
primStr FromInteger = "fromInteger"
primStr ToInteger = "toInteger"
primStr ToInt = "toInt"
primStr Error = "error"
primStr Undefined = "undefined"
primStr BindFunc = "BindFunc"

strToPrim :: T.Text -> Maybe Primitive
strToPrim "not" = Just Not
strToPrim "&&" = Just And
strToPrim "||" = Just Or
strToPrim ">=" = Just Ge
strToPrim ">" = Just Gt
strToPrim "==" = Just Eq
strToPrim "/=" = Just Neq
strToPrim "<=" = Just Le
strToPrim "<" = Just Lt
strToPrim "+" = Just Plus
strToPrim "-" = Just Minus
strToPrim "*" = Just Mult
strToPrim "quot" = Just Quot
strToPrim "/" = Just Div
strToPrim "mod" = Just Mod
strToPrim "negate" = Just Negate
strToPrim "sqrt" = Just SqRt
strToPrim "error" = Just Error
strToPrim "implies" = Just Implies
strToPrim "iff" = Just Iff
strToPrim _ = Nothing

findPrim :: Primitive -> [(Name, Type)] -> (Name, Type)
findPrim prim [] = error $ "findPrim: not found: " ++ (T.unpack $ primStr prim)
findPrim prim (p@(Name occ _ _ _, _):ps) =
    if primStr prim == occ then p else findPrim prim ps

mkRawPrim :: [(Name, Type)] -> Name -> Expr
mkRawPrim primtys name@(Name occ _ _ _) = 
        case prim of
            Just _ -> foldr (Lam TypeL) cases ids
            Nothing -> Prim Undefined TyBottom
  where
    prim = strToPrim occ

    ty = snd . head $ filter (\p -> name == fst p) primtys
    (forall_ids, ty') = splitTyForAlls ty
    fun_tys = splitTyFuns ty'

    tys = (map typeOf forall_ids) ++ fun_tys

    ids = map (\(i, t) -> Id (Name "a" Nothing i Nothing) t) $ zip [1..] (init tys)
    binds = map (\(i, t) -> Id (Name "b" Nothing i Nothing) t) $ zip [1..] (init tys)

    varIds = map Var ids
    varBinds = map Var binds

    apps = foldl' App (Prim (case prim of
                                    Just p -> p
                                    Nothing -> error $ "PRIM = " ++ show prim) ty) varBinds

    cases = foldr (\(i, b) e -> Case i b [Alt Default e]) apps (zip varIds binds)

-- | Primitive lookup helpers

mkPrim :: Primitive -> E.ExprEnv -> Expr
mkPrim p eenv = case (inClasses, inNum, inPrelude, inClasses2, inBase2, inReal) of
    (Just e, _, _, _, _, _) -> e
    (_, Just e, _, _, _, _) -> e
    (_, _, Just e, _, _, _) -> e
    (_, _, _, Just e, _, _) -> e
    (_, _, _, _, Just e, _) -> e
    (_, _, _, _, _, Just e) -> e
    _ -> error $ "Unrecognized prim " ++ show p ++ " " ++ show (primStr p)
    where
        inClasses = E.occLookup (primStr p) (Just "GHC.Classes") eenv
        inNum = E.occLookup (primStr p) (Just "GHC.Num") eenv
        inPrelude = E.occLookup (primStr p) (Just "Prelude") eenv
        inClasses2 = E.occLookup (primStr p) (Just "GHC.Classes2") eenv
        inBase2 = E.occLookup (primStr p) (Just "GHC.Base2") eenv
        inReal = E.occLookup (primStr p) (Just "GHC.Real") eenv

mkGe :: KnownValues -> E.ExprEnv -> Expr
mkGe kv eenv = eenv E.! (geFunc kv)

mkGt :: KnownValues -> E.ExprEnv -> Expr
mkGt kv eenv = eenv E.! (gtFunc kv)

mkEq :: KnownValues -> E.ExprEnv -> Expr
mkEq kv eenv = eenv E.! (eqFunc kv)

mkEq' :: KnownValues -> Expr
mkEq' kv = Var (Id (eqFunc kv) TyBottom)

mkNeq :: KnownValues -> E.ExprEnv -> Expr
mkNeq kv eenv = eenv E.! (neqFunc kv)

mkLt :: KnownValues -> E.ExprEnv -> Expr
mkLt kv eenv = eenv E.! (ltFunc kv)

mkLe :: KnownValues -> E.ExprEnv -> Expr
mkLe kv eenv = eenv E.! (leFunc kv)

mkAnd :: KnownValues -> E.ExprEnv -> Expr
mkAnd kv eenv = eenv E.! (andFunc kv)

mkOr :: KnownValues -> E.ExprEnv -> Expr
mkOr kv eenv = eenv E.! (orFunc kv)

mkNot :: KnownValues -> E.ExprEnv -> Expr
mkNot kv eenv = eenv E.! (notFunc kv)

mkPlus :: KnownValues -> E.ExprEnv -> Expr
mkPlus kv eenv = eenv E.!  (plusFunc kv)

mkMinus :: KnownValues -> E.ExprEnv -> Expr
mkMinus kv eenv = eenv E.! (minusFunc kv)

mkMult :: KnownValues -> E.ExprEnv -> Expr
mkMult kv eenv = eenv E.! (timesFunc kv)

mkDiv :: KnownValues -> E.ExprEnv -> Expr
mkDiv kv eenv = eenv E.! (divFunc kv)

mkMod :: KnownValues -> E.ExprEnv -> Expr
mkMod kv eenv = eenv E.! (modFunc kv)

mkNegate :: KnownValues -> E.ExprEnv -> Expr
mkNegate kv eenv = eenv E.! (negateFunc kv)

mkImplies :: E.ExprEnv -> Expr
mkImplies = mkPrim Implies

mkIff :: E.ExprEnv -> Expr
mkIff = mkPrim Iff

mkFromInteger :: KnownValues -> E.ExprEnv -> Expr
mkFromInteger kv eenv = eenv E.! (fromIntegerFunc kv)

mkToInteger :: KnownValues -> E.ExprEnv -> Expr
mkToInteger kv eenv = eenv E.! (toIntegerFunc kv)

-- Primitives on primitive types
mkEqPrimType :: Type -> KnownValues -> Expr
mkEqPrimType t kv =
    Prim Eq $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))

mkEqPrimInt :: KnownValues -> Expr
mkEqPrimInt = mkEqPrimType TyLitInt

mkEqPrimFloat :: KnownValues -> Expr
mkEqPrimFloat = mkEqPrimType TyLitFloat

mkEqPrimDouble :: KnownValues -> Expr
mkEqPrimDouble = mkEqPrimType TyLitDouble

mkEqPrimChar :: KnownValues -> Expr
mkEqPrimChar = mkEqPrimType TyLitChar

mkGePrimInt :: KnownValues -> Expr
mkGePrimInt kv = Prim Ge $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))
    where
        t = TyLitInt

mkLePrimInt :: KnownValues -> Expr
mkLePrimInt kv = Prim Le $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))
    where
        t = TyLitInt

mkAndPrim :: KnownValues -> Expr
mkAndPrim kv = Prim And $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))
    where t = (TyCon (KV.tyBool kv) TYPE)

