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
                                              , mkToIntegerE ) where

import G2.Internals.Language.Primitives
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import G2.Internals.Language.Monad.Support

appExpr :: (ExprEnv -> Expr) -> StateM t Expr
appExpr f = return . f =<< expr_envM

mkGeE :: StateM t Expr
mkGeE = appExpr mkGe

mkGtE :: StateM t Expr
mkGtE = appExpr mkGt

mkEqE :: StateM t Expr
mkEqE = appExpr mkEq

mkNeqE :: StateM t Expr
mkNeqE = appExpr mkNeq

mkLtE :: StateM t Expr
mkLtE = appExpr mkLt

mkLeE :: StateM t Expr
mkLeE = appExpr mkLe

mkAndE :: StateM t Expr
mkAndE = appExpr mkAnd

mkOrE :: StateM t Expr
mkOrE = appExpr mkOr

mkNotE :: StateM t Expr
mkNotE = appExpr mkNot

mkPlusE :: StateM t Expr
mkPlusE = appExpr mkPlus

mkMinusE :: StateM t Expr
mkMinusE = appExpr mkMinus

mkMultE :: StateM t Expr
mkMultE = appExpr mkMult

mkDivE :: StateM t Expr
mkDivE = appExpr mkDiv

mkModE :: StateM t Expr
mkModE = appExpr mkMod

mkNegateE :: StateM t Expr
mkNegateE = appExpr mkNegate

mkImpliesE :: StateM t Expr
mkImpliesE = appExpr mkImplies

mkIffE :: StateM t Expr
mkIffE = appExpr mkIff

mkFromIntegerE :: StateM t Expr
mkFromIntegerE = appExpr mkFromInteger

mkToIntegerE :: StateM t Expr
mkToIntegerE = appExpr mkToInteger
