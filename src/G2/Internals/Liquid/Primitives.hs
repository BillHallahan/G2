{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Primitives where

import G2.Internals.Language.Expr
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

mkLHPrim :: Primitive -> Type -> Expr -> Expr -> Expr
mkLHPrim p t e1 e2 =
    let
        b1 = Name "b" Nothing 1
        b2 = Name "b" Nothing 2
    
        i1 = Id b1 $ typeOf e1
        i2 = Id b2 $ typeOf e2
    in
    Case e1 i1 [Alt Default 
        $ Case e2 i2 [Alt Default 
            (mkApp [Prim p t, Var i1, Var i2])]]

boolBoolBool :: KV.KnownValues -> Type
boolBoolBool kv =
    let
        tyB = tyBool kv
    in
    TyFun tyB $ TyFun tyB tyB

mkLHGe :: Expr -> Expr -> Expr
mkLHGe = mkLHPrim Ge TyUnknown

mkLHGt :: Expr -> Expr -> Expr
mkLHGt = mkLHPrim Gt TyUnknown

mkLHEq :: Expr -> Expr -> Expr
mkLHEq = mkLHPrim Eq TyUnknown

mkLHNeq :: Expr -> Expr -> Expr
mkLHNeq = mkLHPrim Neq TyUnknown

mkLHLt :: Expr -> Expr -> Expr
mkLHLt = mkLHPrim Lt TyUnknown

mkLHLe :: Expr -> Expr -> Expr
mkLHLe = mkLHPrim Le TyUnknown

mkLHAnd :: KV.KnownValues -> Expr -> Expr -> Expr
mkLHAnd kv = mkLHPrim And (boolBoolBool kv)

mkLHOr :: KV.KnownValues -> Expr -> Expr -> Expr
mkLHOr kv = mkLHPrim Or (boolBoolBool kv)

mkLHImplies :: KV.KnownValues -> Expr -> Expr -> Expr
mkLHImplies kv = mkLHPrim Implies (boolBoolBool kv)

mkLHIff :: KV.KnownValues -> Expr -> Expr -> Expr
mkLHIff kv = mkLHPrim Iff (boolBoolBool kv)
