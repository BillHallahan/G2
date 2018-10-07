module G2.Internals.Language.Monad.Primitives ( mkGeE
                                              , mkGtE
                                              , mkEqE
                                              , mkNeqE
                                              , mkLtE
                                              , mkLeE
                                              , mkAndE
                                              , mkOrE
                                              , mkNotE
                                              , mkPlusE
                                              , mkMinusE
                                              , mkMultE
                                              , mkDivE
                                              , mkModE
                                              , mkNegateE
                                              , mkImpliesE
                                              , mkIffE
                                              , mkFromIntegerE
                                              , mkToIntegerE
                                              , mkEqPrimIntE
                                              , mkEqPrimFloatE
                                              , mkEqPrimDoubleE
                                              , mkEqPrimCharE ) where

import G2.Internals.Language.Primitives
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import G2.Internals.Language.Monad.Support

appExpr :: ExState s m => (ExprEnv -> Expr) -> m Expr
appExpr f = return . f =<< exprEnv

mkGeE :: ExState s m => m Expr
mkGeE = appExpr mkGe

mkGtE :: ExState s m => m Expr
mkGtE = appExpr mkGt

mkEqE :: ExState s m => m Expr
mkEqE = appExpr mkEq

mkNeqE :: ExState s m => m Expr
mkNeqE = appExpr mkNeq

mkLtE :: ExState s m => m Expr
mkLtE = appExpr mkLt

mkLeE :: ExState s m => m Expr
mkLeE = appExpr mkLe

mkAndE :: ExState s m => m Expr
mkAndE = appExpr mkAnd

mkOrE :: ExState s m => m Expr
mkOrE = appExpr mkOr

mkNotE :: ExState s m => m Expr
mkNotE = appExpr mkNot

mkPlusE :: ExState s m => m Expr
mkPlusE = appExpr mkPlus

mkMinusE :: ExState s m => m Expr
mkMinusE = appExpr mkMinus

mkMultE :: ExState s m => m Expr
mkMultE = appExpr mkMult

mkDivE :: ExState s m => m Expr
mkDivE = appExpr mkDiv

mkModE :: ExState s m => m Expr
mkModE = appExpr mkMod

mkNegateE :: ExState s m => m Expr
mkNegateE = appExpr mkNegate

mkImpliesE :: ExState s m => m Expr
mkImpliesE = appExpr mkImplies

mkIffE :: ExState s m => m Expr
mkIffE = appExpr mkIff

mkFromIntegerE :: ExState s m => m Expr
mkFromIntegerE = appExpr mkFromInteger

mkToIntegerE :: ExState s m => m Expr
mkToIntegerE = appExpr mkToInteger

appKV :: ExState s m => (KnownValues -> Expr) -> m Expr
appKV f = return . f =<< knownValues

mkEqPrimIntE :: ExState s m => m Expr
mkEqPrimIntE = appKV mkEqPrimInt

mkEqPrimFloatE :: ExState s m => m Expr
mkEqPrimFloatE = appKV mkEqPrimFloat

mkEqPrimDoubleE :: ExState s m => m Expr
mkEqPrimDoubleE = appKV mkEqPrimDouble

mkEqPrimCharE :: ExState s m => m Expr
mkEqPrimCharE = appKV mkEqPrimChar
