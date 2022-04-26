module G2.Language.Monad.Primitives ( mkGeE
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

import G2.Language.KnownValues
import G2.Language.Primitives
import G2.Language.Syntax
import G2.Language.Typing

import G2.Language.Monad.ExprEnv
import G2.Language.Monad.Support

mkGeE :: ExState s m => m Expr
mkGeE = appKVEEnv geFunc

mkGtE :: ExState s m => m Expr
mkGtE = appKVEEnv gtFunc

mkEqE :: ExState s m => m Expr
mkEqE = appKVEEnv eqFunc

mkNeqE :: ExState s m => m Expr
mkNeqE = appKVEEnv neqFunc

mkLtE :: ExState s m => m Expr
mkLtE = appKVEEnv ltFunc

mkLeE :: ExState s m => m Expr
mkLeE = appKVEEnv leFunc

mkAndE :: ExState s m => m Expr
mkAndE = appKVEEnv andFunc

mkOrE :: ExState s m => m Expr
mkOrE = appKVEEnv orFunc

mkNotE :: ExState s m => m Expr
mkNotE = appKVEEnv notFunc

mkPlusE :: ExState s m => m Expr
mkPlusE = appKVEEnv plusFunc

mkMinusE :: ExState s m => m Expr
mkMinusE = appKVEEnv minusFunc

mkMultE :: ExState s m => m Expr
mkMultE = appKVEEnv timesFunc

mkDivE :: ExState s m => m Expr
mkDivE = appKVEEnv divFunc

mkModE :: ExState s m => m Expr
mkModE = appKVEEnv modFunc

mkNegateE :: ExState s m => m Expr
mkNegateE = appKVEEnv negateFunc

mkImpliesE :: ExState s m => m Expr
mkImpliesE = appKVEEnv impliesFunc

mkIffE :: ExState s m => m Expr
mkIffE = appKVEEnv iffFunc

mkFromIntegerE :: ExState s m => m Expr
mkFromIntegerE = appKVEEnv fromIntegerFunc

mkToIntegerE :: ExState s m => m Expr
mkToIntegerE = appKVEEnv toIntegerFunc

appKVEEnv :: ExState s m => (KnownValues -> Name) -> m Expr
appKVEEnv f = do
    n <- return . f =<< knownValues
    e <- lookupE n
    case e of
        Just e' -> return . Var $ Id n (typeOf e')
        Nothing -> error "appKVEEnv: not found"

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
