module G2.Language.Primitives ( mkGe
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
                              , mkLePrimInt

                              , mkEqPrimType
                              , mkOrPrim
                              , mkImpliesPrim
                              , mkNotPrim
                              
                              , mkStringAppend
                              , mkStringLen) where

import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues as KV
import G2.Language.Syntax
import qualified G2.Language.Typing as T

mkGe :: KnownValues -> E.ExprEnv -> Expr
mkGe kv eenv = eenv E.! (geFunc kv)

mkGt :: KnownValues -> E.ExprEnv -> Expr
mkGt kv eenv = eenv E.! (gtFunc kv)

mkEq :: KnownValues -> E.ExprEnv -> Expr
mkEq kv eenv = eenv E.! (eqFunc kv)

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

mkImplies :: KnownValues -> E.ExprEnv -> Expr
mkImplies kv eenv = eenv E.! (impliesFunc kv)

mkIff :: KnownValues -> E.ExprEnv -> Expr
mkIff kv eenv = eenv E.! (iffFunc kv)

mkFromInteger :: KnownValues -> E.ExprEnv -> Expr
mkFromInteger kv eenv = eenv E.! (fromIntegerFunc kv)

mkToInteger :: KnownValues -> E.ExprEnv -> Expr
mkToInteger kv eenv = eenv E.! (toIntegerFunc kv)

-- Primitives on primitive types
mkEqPrimType :: Type -> KnownValues -> Expr
mkEqPrimType t kv | t == TyLitFloat ||  t == TyLitDouble = Prim FpEq $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))
mkEqPrimType t kv = Prim Eq $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))

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

mkOrPrim :: KnownValues -> Expr
mkOrPrim kv = Prim Or $ TyFun t (TyFun t (TyCon (KV.tyBool kv) TYPE))
    where t = (TyCon (KV.tyBool kv) TYPE)

mkNotPrim :: KnownValues -> Expr
mkNotPrim kv = Prim Not $ TyFun t (TyCon (KV.tyBool kv) TYPE)
    where t = (TyCon (KV.tyBool kv) TYPE)

mkImpliesPrim :: KnownValues -> Expr
mkImpliesPrim kv = Prim Implies $ TyFun t (TyFun t t)
    where t = (TyCon (KV.tyBool kv) TYPE)

mkStringAppend :: KnownValues -> Expr
mkStringAppend kv = Prim StrAppend $ TyFun t (TyFun t t)
    where t = TyApp (T.tyList kv) (T.tyChar kv)

mkStringLen :: KnownValues -> Expr
mkStringLen kv = Prim StrLen $ TyFun t TyLitInt
    where t = TyApp (T.tyList kv) (T.tyChar kv)