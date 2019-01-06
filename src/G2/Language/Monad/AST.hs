{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Language.Monad.AST where

import G2.Language.AST
import G2.Language.Syntax

import qualified Data.Text as T

class AST t => ASTM t where
    modifyChildrenM :: Monad m => (t -> m t) -> t -> m t

modifyM :: (ASTM t, Monad m) => (t -> m t) -> t -> m t
modifyM f t = go t
    where
        go t' = modifyChildrenM go =<< f t'

modifyFixM :: (ASTM t, Monad m, Eq t) => (t -> m t) -> t -> m t
modifyFixM f e = do
    e' <- f e
    if e == e'
        then modifyChildrenM (modifyFixM f) e'
        else modifyFixM f e'

class (ASTM t, ASTContainer c t) => ASTContainerM c t where
    modifyContainedASTsM :: Monad m => (t -> m t) -> c -> m c

modifyASTsM :: (ASTContainerM c e, Monad m) => (e -> m e) -> c -> m c
modifyASTsM f = modifyContainedASTsM (modifyM f)

-- | Instance ASTContainerM of Itself
--   Every ASTM is defined as an ASTContainerM of itself. Generally, functions
--   should be written using the ASTContainerM typeclass.
instance ASTM t => ASTContainerM t t where
    modifyContainedASTsM f t = f t

instance ASTM Expr where
    modifyChildrenM f (App fx ax) = do
        fx' <- f fx
        ax' <- f ax
        return $ App fx' ax'
    modifyChildrenM f (Lam u b e) = return . Lam u b =<< f e
    modifyChildrenM f (Let bind e) = do
        bind' <- modifyContainedASTsM f bind
        return . Let bind' =<< f e
    modifyChildrenM f (Case m b as) = do
        m' <- f m
        return . Case m' b =<< modifyContainedASTsM f as
    modifyChildrenM  f (Cast e c) = do
        e' <- f e
        return $ Cast e' c
    modifyChildrenM f (Tick t e) = return . Tick t =<< f e
    modifyChildrenM f (NonDet es) = return . NonDet =<< mapM f es
    modifyChildrenM f (Assume is e1 e2) = do
        is' <- modifyContainedASTsM f is
        e1' <- f e1
        e2' <- f e2
        return $ Assume is' e1' e2'
    modifyChildrenM f (Assert is e1 e2) = do
        is' <- modifyContainedASTsM f is
        e1' <- f e1
        e2' <- f e2
        return $ Assert is' e1' e2'
    modifyChildrenM _ e = return e

instance ASTM Type where
    modifyChildrenM f (TyVar i) = return . TyVar =<< modifyContainedASTsM f i
    modifyChildrenM f (TyFun tf ta) = do
        tf' <- f tf
        ta' <- f ta
        return $ TyFun tf' ta'
    modifyChildrenM f (TyApp tf ta) = do
        tf' <- f tf
        ta' <- f ta
        return $ TyApp tf' ta'
    modifyChildrenM f (TyCon b ts) =
        return . TyCon b =<< f ts
    modifyChildrenM f (TyForAll b t) = do
        b' <- modifyContainedASTsM f b
        return . TyForAll b' =<< modifyChildrenM f t
    modifyChildrenM _ t = return t

instance ASTContainerM Expr Type where
    modifyContainedASTsM f (Var i) = return . Var =<< modifyContainedASTsM f i
    modifyContainedASTsM f (Prim p t) = return . Prim p =<< f t
    modifyContainedASTsM f (Data dc) = return . Data =<< modifyContainedASTsM f dc
    modifyContainedASTsM f (App fx ax) = do
        fx' <- modifyContainedASTsM f fx
        ax' <- modifyContainedASTsM f ax
        return $ App fx' ax'
    modifyContainedASTsM f (Lam u b e) = do
        b' <- modifyContainedASTsM f b
        e' <- modifyContainedASTsM f e
        return $ Lam u b' e'
    modifyContainedASTsM f (Let bnd e) = do
        bnd' <- modifyContainedASTsM f bnd
        e' <- modifyContainedASTsM f e
        return $ Let bnd' e'
    modifyContainedASTsM f (Case m i as) = do
        m' <- modifyContainedASTsM f m
        i' <- modifyContainedASTsM f i
        as' <- modifyContainedASTsM f as
        return $ Case m' i' as'
    modifyContainedASTsM f (Type t) = return . Type =<< f t
    modifyContainedASTsM f (Cast e c) = do
        e' <- modifyContainedASTsM f e
        c' <- modifyContainedASTsM f c
        return $ Cast e' c'
    modifyContainedASTsM f (Coercion c) = return . Coercion =<< modifyContainedASTsM f c
    modifyContainedASTsM f (Tick t e) = return . Tick t =<< modifyContainedASTsM f e
    modifyContainedASTsM f (NonDet es) = return . NonDet =<< modifyContainedASTsM f es
    modifyContainedASTsM f (Assume is e1 e2) = do
        is' <- modifyContainedASTsM f is
        e1' <- modifyContainedASTsM f e1
        e2' <- modifyContainedASTsM f e2
        return $ Assume is' e1' e2'
    modifyContainedASTsM f (Assert is e1 e2) = do
        is' <- modifyContainedASTsM f is
        e1' <- modifyContainedASTsM f e1
        e2' <- modifyContainedASTsM f e2
        return $ Assert is' e1' e2'
    modifyContainedASTsM _ e = return e

instance ASTContainerM c e => ASTContainerM [c] e where
    modifyContainedASTsM f = mapM (modifyContainedASTsM f)

instance ASTContainerM c e => ASTContainerM (Maybe c) e where
    modifyContainedASTsM f = mapM (modifyContainedASTsM f)

instance (ASTContainerM c t, ASTContainerM d t) => ASTContainerM (c, d) t where
    modifyContainedASTsM f (x, y) = do
        x' <- modifyContainedASTsM f x
        y' <- modifyContainedASTsM f y
        return (x', y')

instance ASTContainerM Id Expr where
    {-# INLINE modifyContainedASTsM #-}
    modifyContainedASTsM _ i = return i

instance ASTContainerM Id Type where
    modifyContainedASTsM f (Id n t) = return . Id n =<< f t

instance ASTContainerM TyBinder Type where
    modifyContainedASTsM f (AnonTyBndr t) = return . AnonTyBndr =<< f t
    modifyContainedASTsM f (NamedTyBndr i) =
        return . NamedTyBndr =<< modifyContainedASTsM f i

instance ASTContainerM DataCon Expr where
    {-# INLINE modifyContainedASTsM #-}
    modifyContainedASTsM _ dc = return dc

instance ASTContainerM DataCon Type where
    modifyContainedASTsM f (DataCon n t) = return . DataCon n =<< f t

instance ASTContainerM AltMatch Expr where
    {-# INLINE modifyContainedASTsM #-}
    modifyContainedASTsM _ am = return am

instance ASTContainerM Alt Expr where
    modifyContainedASTsM f (Alt a e) = do
        e' <- modifyContainedASTsM f e
        return $ Alt a e'

instance ASTContainerM AltMatch Type where
    modifyContainedASTsM f (DataAlt dc i) = do
        dc' <- modifyContainedASTsM f dc
        i' <- modifyContainedASTsM f i
        return $ DataAlt dc' i'
    modifyContainedASTsM _ am = return am

instance ASTContainerM Alt Type where
    modifyContainedASTsM f (Alt a e) = do
        a' <- modifyContainedASTsM f a
        e' <- modifyContainedASTsM f e
        return $ Alt a' e'

instance ASTContainerM Coercion Type where
    modifyContainedASTsM f (t1 :~ t2) = do
        t1' <- f t1
        t2' <- f t2
        return $ t1' :~ t2'

instance ASTContainerM FuncCall Expr where
    modifyContainedASTsM f fc@(FuncCall { arguments = as, returns = r}) = do
        as' <- modifyContainedASTsM f as
        r' <- modifyContainedASTsM f r
        return $ fc { arguments = as', returns = r' }

instance ASTContainerM FuncCall Type where
    modifyContainedASTsM f fc@(FuncCall { arguments = as, returns = r}) = do
        as' <- modifyContainedASTsM f as
        r' <- modifyContainedASTsM f r
        return $ fc { arguments = as', returns = r' }

instance ASTContainerM T.Text Expr where
    modifyContainedASTsM _ = return

instance ASTContainerM T.Text Type where
    modifyContainedASTsM _ = return
