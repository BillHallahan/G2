module G2.Core.CoreManipulator where

import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Monoid as Mon

{-
modifyE f g e x eases mapping over or evaluating an expression in a tree like manner

It allows the passing of information in an arbitrary structure, a, which is initialized
to the value of x.

f x e returns a new expression e', and some value of a, x'.  Each expression, e'', in e',
is then replaced with f e'' x', recursively.

modifyT f g e x does the same, except it works on Types
-}

class Manipulatable m where
    modifyE:: Monoid a => (a -> Expr -> (Expr, a)) -> m -> a -> (m, a)
    modifyExpr :: (Expr -> Expr) -> m -> m
    modifyExpr' :: Monoid a => (a -> Expr -> (Expr, a)) -> m -> m
    modifyExpr'' :: Monoid a => (a -> Expr -> (Expr, a)) -> m -> a-> m

    modifyT :: Monoid a => (a -> Type -> (Type, a)) -> m -> a -> (m, a)
    modifyType :: (Type -> Type) -> m -> m
    modifyType' :: Monoid a => (a -> Type -> (Type, a)) -> m -> m
    modifyType'' :: Monoid a => (a -> Type -> (Type, a)) -> m -> a -> m

    evalExpr :: Monoid a => (Expr -> a) -> m -> a
    evalExpr' :: Monoid a => (a -> Expr -> a) -> m -> a
    evalExpr'' :: Monoid a => (a -> Expr -> a) -> m -> a -> a

    evalType :: Monoid a => (Type -> a) -> m -> a
    evalType' :: Monoid a =>  (a -> Type -> a) -> m -> a
    evalType'' :: Monoid a =>  (a -> Type -> a) -> m -> a -> a

    --default implementations
    modifyExpr f e = modifyExpr' (\_ e' -> (f e', ())) e
    modifyExpr' f e = fst . modifyE f e $ mempty
    modifyExpr'' f e x = fst . modifyE f e $ x

    modifyType f t = modifyType' (\_ t' -> (f t', ())) t
    modifyType' f t = fst . modifyT f t $ mempty
    modifyType'' f e x = fst . modifyT f e $ x

    evalExpr f e = evalExpr' (\_ e' -> f e') e
    evalExpr' f e = snd . modifyE (\a' e' -> (e', f a' e')) e $ mempty
    evalExpr'' f e x = snd . modifyE (\a' e' -> (e', f a' e')) e $ x

    evalType f t = evalType' (\_ t' -> f t') t
    evalType' f t = snd . modifyT (\a' t' -> (t', f a' t')) t $ mempty
    evalType'' f t x = snd . modifyT (\a' t' -> (t', f a' t')) t $ x

instance Manipulatable Expr where
    modifyE f e x =
        let
            (e', x') = f x e
            (e'', x'') = modify' f e' (x `mappend` x')
        in
        (e'', x' `mappend` x'')
        where
            modify' :: Monoid a => (a -> Expr -> (Expr, a)) -> Expr -> a -> (Expr, a)
            modify' f (Lam n e t) x =
                let
                    (e', x') = modifyE f e x
                in
                (Lam n e' t, x')
            modify' f (App e1 e2) x =
                let 
                    (e1', x') = modifyE f e1 x
                    (e2', x'') = modifyE f e2 x
                in
                (App e1' e2', x' `mappend` x'')
            modify' f (Case e ae t) x =
                let
                    (e', x') = modifyE f e x
                    (ae', x'') = modifyE f ae x
                in
                (Case e' ae' t, x' `mappend` x'')
            modify' _ e x = (e, mempty)

    --This is similar to modifyTs, but it acts on all Types in a given Expr
    modifyT f e x = modifyE (f' f) e x
        where
            f' :: Monoid a => (a ->  Type -> (Type, a)) -> a -> Expr -> (Expr, a)
            f' f x (Var n t) =
                let
                    (t', x') = modifyT f t x
                in
                (Var n t', x')
            f' f x (Lam n e t) =
                let
                    (t', x') = modifyT f t x
                in
                (Lam n e t', x')
            f' f x (DCon d) =
                let
                    (d', x') = modifyT f d x
                in
                (DCon d', x')
            f' f x (Case e ae t) =
                let
                    (t', x') = modifyT f t x
                in
                (Case e ae t', x')
            f' f x (Type t) =
                let
                    (t', x') = modifyT f t x
                in
                (Type t', x')
            f' _ _ e = (e, mempty)

instance Manipulatable Type where
    modifyE _ e x = (e, x)

    modifyT f t x =
        let
            (t', x') = f x t
            (t'', x'') = modifyT' f t' x'
        in
        (t'', x' `mappend` x'')
        where
            modifyT' :: Monoid a => (a -> Type -> (Type, a)) -> Type -> a -> (Type, a)
            modifyT' f (TyFun t1 t2) x =
                let 
                    (t1', x') = modifyT f t1 x
                    (t2', x'') = modifyT f t2 x
                in
                (TyFun t1' t2', x' `mappend` x'')
            modifyT' f (TyApp t1 t2) x =
                let 
                    (t1', x') = modifyT f t1 x
                    (t2', x'') = modifyT f t2 x
                in
                (TyApp t1' t2', x' `mappend` x'')
            modifyT' f (TyConApp n ts) x =
                let
                    tsx = map (\t' -> modifyT f t' x) ts
                    ts' = map fst tsx
                    x' = mconcat (map snd tsx)
                in
                (TyConApp n ts', x')
            modifyT' f (TyAlg n d) x =
                let
                    (d', x') = modifyT f d x
                in
                (TyAlg n d', x')
            modifyT' f (TyForAll n t) x =
                let
                    (t', x') = modifyT f t x 
                in
                (TyForAll n t', x `mappend` x')
            modifyT' _ t _ = (t, mempty)

instance (Manipulatable a, Manipulatable b) => Manipulatable (a, b) where
    modifyE f (t1, t2) x = 
        let
            (t1', x1') = modifyE f t1 x
            (t2', x2') = modifyE f t2 x
        in
        ((t1', t2'), x1' `mappend` x2')

    modifyT f (t1, t2) x = 
        let
            (t1', x1') = modifyT f t1 x
            (t2', x2') = modifyT f t2 x
        in
        ((t1', t2'), x1' `mappend` x2')

instance (Manipulatable a
          , Manipulatable b
          , Manipulatable c) => Manipulatable (a, b, c) where
    modifyE f (t1, t2, t3) x = 
        let
            (t1', x1') = modifyE f t1 x
            (t2', x2') = modifyE f t2 x
            (t3', x3') = modifyE f t3 x
        in
        ((t1', t2', t3'), mconcat[x1', x2', x3'])

    modifyT f (t1, t2, t3) x = 
        let
            (t1', x1') = modifyT f t1 x
            (t2', x2') = modifyT f t2 x
            (t3', x3') = modifyT f t3 x
        in
        ((t1', t2', t3'), mconcat [x1', x2', x3'])

instance (Manipulatable a
          , Manipulatable b
          , Manipulatable c
          , Manipulatable d) => Manipulatable (a, b, c, d) where
    modifyE f (t1, t2, t3, t4) x = 
        let
            (t1', x1') = modifyE f t1 x
            (t2', x2') = modifyE f t2 x
            (t3', x3') = modifyE f t3 x
            (t4', x4') = modifyE f t4 x
        in
        ((t1', t2', t3', t4'), mconcat [x1', x2', x3', x4'])

    modifyT f (t1, t2, t3, t4) x = 
        let
            (t1', x1') = modifyT f t1 x
            (t2', x2') = modifyT f t2 x
            (t3', x3') = modifyT f t3 x
            (t4', x4') = modifyT f t4 x
        in
        ((t1', t2', t3', t4'), mconcat [x1', x2', x3', x4'])

instance Manipulatable Alt where
    modifyE f (Alt (dc, n)) x =
        let
            (dc', x') = modifyE f dc x
        in
        (Alt(dc', n), x')

    modifyT f (Alt (dc, n)) x =
        let
            (dc', x') = modifyT f dc x
        in
        (Alt(dc', n), x')

instance Manipulatable DataCon where
    modifyE f dc x = (dc, mempty)

    modifyT f (DC (n, i, t, tx)) x = 
        let
            (t', x') = modifyT f t x
            (tx', x'') = modifyT f tx x
        in
        (DC (n, i, t', tx'), x' `mappend` x'')


instance Manipulatable a => Manipulatable [a] where
    modifyE f e x =
        let
            (e', x') = unzip . map (\e'' -> modifyE f e'' x) $ e
        in
        (e', mconcat x')

    modifyT f t x =
        let
            (t', x') = unzip . map (\t'' -> modifyT f t'' x) $ t
        in
        (t', mconcat x')

instance Manipulatable v => Manipulatable (M.Map k v) where
    modifyE f e x =
        let
            res = M.map (\e'' -> modifyE f e'' x) $ e
            e' = M.map fst res
            x' = map snd . M.elems $ res
        in
        (e', mconcat x')

    modifyT f e x =
        let
            res = M.map (\e'' -> modifyT f e'' x) $ e
            e' = M.map fst res
            x' = map snd . M.elems $ res
        in
        (e', mconcat x')

--This is similar to modifyTs in the typeclass for expression, but it alllows access to the expression as well
--This is very similar to that def, might be a neater way to define it?
modifyTsInExpr :: Monoid a => (Expr -> a -> Type -> (Type, a)) -> Expr -> a -> (Expr, a)
modifyTsInExpr f e x = modifyE (f' f) e x
    where
        f' :: Monoid a => (Expr -> a ->  Type -> (Type, a))-> a -> Expr -> (Expr, a)
        f' f x v@(Var n t) =
            let
                (t', x') = modifyT (f v) t x
            in
            (Var n t', x')
        f' f x lam@(Lam n e t) =
            let
                (t', x') = modifyT (f lam) t x
            in
            (Lam n e t', x')
        f' f x e@(DCon d) =
            let
                (d', x') = modifyT (f e) d x
            in
            (DCon d', x')
        f' f x ca@(Case e ae t) =
            let
                (t', x') = modifyT (f ca) t x
            in
            (Case e ae t', x')
        f' f x e@(Type t) =
            let
                (t', x') = modifyT (f e) t x
            in
            (Type t', x')
        f' _ _ e = (e, mempty)

-- --These are special cases of modifyTsInExpr
modifyTypesInExpr :: (Type -> Type) -> Expr -> Expr
modifyTypesInExpr f e = modifyTypesInExpr' (\_ t' -> f t') e

modifyTypesInExpr' :: (Expr -> Type -> Type) -> Expr -> Expr
modifyTypesInExpr' f t = modifyTypesInExpr'' (\e _ t' -> (f e t', ())) t ()

modifyTypesInExpr'' :: Monoid a => (Expr -> a -> Type -> (Type, a)) -> Expr -> a -> Expr
modifyTypesInExpr'' f t x = fst . modifyTsInExpr f t $ x

evalTypesInExpr :: Monoid a => (Type -> a) -> Expr -> a -> a
evalTypesInExpr f e x = evalTypesInExpr' (\_ t' -> f t') e x

evalTypesInExpr' ::  Monoid a => (Expr -> Type -> a) -> Expr -> a -> a
evalTypesInExpr' f e x = evalTypesInExpr'' (\e' _ t' -> f e' t') e x

evalTypesInExpr'' ::  Monoid a => (Expr -> a -> Type -> a) -> Expr -> a -> a
evalTypesInExpr'' f e x = snd . modifyTsInExpr (\e' a' t' -> (t', f e' a' t')) e $ x