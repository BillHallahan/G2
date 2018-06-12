module G2.Internals.Language.Monad.Expr ( mkDCTrueM
                                        , mkDCFalseM
                                        , mkDCIntE
                                        , mkDCIntegerE
                                        , mkDCFloatE
                                        , mkDCDoubleE
                                        , mkTrueE
                                        , mkFalseE
                                        , mkConsE
                                        , mkEmptyE ) where

import G2.Internals.Language.Expr
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import G2.Internals.Language.Monad.Support

appKVTEnv :: ExState s m => (KnownValues -> TypeEnv -> a) -> m a
appKVTEnv f = do
    kv <- knownValues
    tenv <- typeEnv
    return $ f kv tenv

mkDCTrueM :: ExState s m => m DataCon
mkDCTrueM = appKVTEnv mkDCTrue

mkDCFalseM :: ExState s m => m DataCon
mkDCFalseM = appKVTEnv mkDCFalse

mkDCIntE :: ExState s m => m Expr
mkDCIntE = appKVTEnv mkDCInt

mkDCIntegerE :: ExState s m => m Expr
mkDCIntegerE = appKVTEnv mkDCInteger

mkDCFloatE :: ExState s m => m Expr
mkDCFloatE = appKVTEnv mkDCFloat

mkDCDoubleE :: ExState s m => m Expr
mkDCDoubleE = appKVTEnv mkDCDouble

mkTrueE :: ExState s m => m Expr
mkTrueE = appKVTEnv mkTrue

mkFalseE :: ExState s m => m Expr
mkFalseE = appKVTEnv mkFalse

mkConsE :: ExState s m => m Expr
mkConsE = appKVTEnv mkCons

mkEmptyE :: ExState s m => m Expr
mkEmptyE = appKVTEnv mkEmpty
