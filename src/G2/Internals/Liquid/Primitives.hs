module G2.Internals.Liquid.Primitives where

import G2.Internals.Language.Expr
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

boolBoolBool :: Type
boolBoolBool = TyFun TyBool $ TyFun TyBool TyBool

mkLHGe :: Expr -> Expr -> Expr
mkLHGe = mkLHPrim Ge TyBottom

mkLHGt :: Expr -> Expr -> Expr
mkLHGt = mkLHPrim Gt TyBottom

mkLHEq :: Expr -> Expr -> Expr
mkLHEq = mkLHPrim Eq TyBottom

mkLHNeq :: Expr -> Expr -> Expr
mkLHNeq = mkLHPrim Neq TyBottom

mkLHLt :: Expr -> Expr -> Expr
mkLHLt = mkLHPrim Lt TyBottom

mkLHLe :: Expr -> Expr -> Expr
mkLHLe = mkLHPrim Le TyBottom

mkLHAnd :: Expr -> Expr -> Expr
mkLHAnd = mkLHPrim And boolBoolBool

mkLHImplies :: Expr -> Expr -> Expr
mkLHImplies = mkLHPrim Implies boolBoolBool

mkLHIff :: Expr -> Expr -> Expr
mkLHIff = mkLHPrim Iff boolBoolBool