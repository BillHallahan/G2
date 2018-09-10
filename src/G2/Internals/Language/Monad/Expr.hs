{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Monad.Expr ( mkDCTrueM
                                        , mkDCFalseM
                                        , mkDCIntE
                                        , mkDCIntegerE
                                        , mkDCFloatE
                                        , mkDCDoubleE
                                        , mkTrueE
                                        , mkFalseE
                                        , mkConsE
                                        , mkEmptyE
                                        , modifyAppTopE ) where

import G2.Internals.Language.Expr
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import G2.Internals.Language.Monad.AST
import G2.Internals.Language.Monad.Support

import Debug.Trace

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

modifyAppTopE :: (Monad m, ASTContainerM c Expr) => (Expr -> m Expr) -> c -> m c
modifyAppTopE f = modifyContainedASTsM (modifyAppTopE' f)

modifyAppTopE' :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyAppTopE' f e@(App _ _) = modifyAppRHSE (modifyAppTopE f) =<< trace ("app = " ++ show e) f e
modifyAppTopE' f e = trace ("going into = " ++ show e) modifyChildrenM (modifyAppTopE' f) e

modifyAppRHSE :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyAppRHSE f (App e1 e2) = do
    e1' <- modifyAppRHSE f e1
    e2' <- f e2
    return $ App e1' e2'
modifyAppRHSE _ e = return e