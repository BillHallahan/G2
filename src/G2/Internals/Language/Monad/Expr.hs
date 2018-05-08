module G2.Internals.Language.Monad.Expr ( mkDCIntE
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

appKVTEnv :: (KnownValues -> TypeEnv -> Expr) -> StateM t Expr
appKVTEnv f = do
	kv <- known_valuesM
	tenv <- type_envM
	return $ f kv tenv

mkDCIntE :: StateM t Expr
mkDCIntE = appKVTEnv mkDCInt

mkDCIntegerE :: StateM t Expr
mkDCIntegerE = appKVTEnv mkDCInteger

mkDCFloatE :: StateM t Expr
mkDCFloatE = appKVTEnv mkDCFloat

mkDCDoubleE :: StateM t Expr
mkDCDoubleE = appKVTEnv mkDCDouble

mkTrueE :: StateM t Expr
mkTrueE = appKVTEnv mkTrue

mkFalseE :: StateM t Expr
mkFalseE = appKVTEnv mkFalse

mkConsE :: StateM t Expr
mkConsE = appKVTEnv mkCons

mkEmptyE :: StateM t Expr
mkEmptyE = appKVTEnv mkEmpty
