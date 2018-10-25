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
                                        , modifyAppTopE
                                        , modifyLamTopE
                                        , insertInLamsE
                                        , etaExpandToE ) where

import G2.Internals.Language.Expr
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support

import G2.Internals.Language.Monad.AST
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

modifyAppTopE :: (Monad m, ASTContainerM c Expr) => (Expr -> m Expr) -> c -> m c
modifyAppTopE f = modifyContainedASTsM (modifyAppTopE' f)

modifyAppTopE' :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyAppTopE' f e@(App _ _) = modifyAppRHSE (modifyAppTopE f) =<< f e
modifyAppTopE' f e = modifyChildrenM (modifyAppTopE' f) e

modifyAppRHSE :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyAppRHSE f (App e1 e2) = do
    e1' <- modifyAppRHSE f e1
    e2' <- f e2
    return $ App e1' e2'
modifyAppRHSE f e = modifyChildrenM f e

modifyLamTopE :: (Monad m, ASTContainerM c Expr) => (Expr -> m Expr) -> c -> m c
modifyLamTopE f = modifyContainedASTsM (modifyLamTopE' f)

modifyLamTopE' :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyLamTopE' f e@(Lam _ _ _) = do
    e' <- f e
    
    modifyLamRHSE (modifyLamTopE' f) e'
modifyLamTopE' f e = modifyChildrenM f e

modifyLamRHSE :: Monad m => (Expr -> m Expr) -> Expr -> m Expr
modifyLamRHSE f (Lam u i e) = return . Lam u i =<< modifyLamRHSE f e
modifyLamRHSE f e = f e

insertInLamsE :: ExState s m => ([Id] -> Expr -> m Expr) -> Expr -> m Expr
insertInLamsE f = insertInLamsE' f []

insertInLamsE' :: ExState s m => ([Id] -> Expr -> m Expr) -> [Id] -> Expr -> m Expr
insertInLamsE' f xs (Lam u i e)  = return . Lam u i =<< insertInLamsE' f (i:xs) e
insertInLamsE' f xs e = f (reverse xs) e

etaExpandToE :: ExState s m => Int -> Expr -> m Expr
etaExpandToE n e = do
    eenv <- exprEnv
    ng <- nameGen

    let (e', ng') = etaExpandTo eenv ng n e

    putNameGen ng'
    return e'