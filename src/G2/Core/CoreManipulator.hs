{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}


module G2.Core.CoreManipulator where

import G2.Core.Language

import qualified Data.Map as M
import qualified Data.Monoid as Mon

{-
Manipulatable e m eases eases mapping over or evaluating expressions or types in a tree like manner
e is either Expr or Type, m is some Type that can contain e, or containers of e.

ModifyG is the most general function.
It takes
f :: Monoid a => a -> e -> (e, a)
et :: m
x :: Monoid a => a

and returns et', x' :: (m, a)

f is applied to et, to obtain (et', x').  Then modifyG f m x' is applied to each m in et'.
This gives us a list, [(m, a)].  The m's are inserted in the respecitve positions in et',
and x' and the a's are mconcated' to get x''.  Then, (et', x'') is returned.

Less specifically, this essentially is walking down a tree of Expr or Types.  f is applied to
each, allowing it's replacement with a new expression or type.  After this replacement,
the walk down the tree continues.  a allows the passing of data back up the tree.
-}

class Manipulatable e m where
    modifyG :: Monoid a => (a -> e -> (e, a)) -> m -> a -> (m, a)
    modify :: (e -> e) -> m -> m
    modify' :: Monoid a => (a -> e -> (e, a)) -> m -> m
    modify'' :: Monoid a => (a -> e -> (e, a)) -> m -> a -> m

    eval :: Monoid a => (e -> a) -> m -> a
    eval' :: Monoid a => (a -> e -> a) -> m -> a
    eval'' :: Monoid a => (a -> e -> a) -> m -> a -> a

    --default implementations
    modify f e = modify' (\_ e' -> (f e', ())) e
    modify' f e = modify'' f e $ mempty
    modify'' f e x = fst . modifyG f e $ x

    eval f e = eval' (\_ e' -> f e') e
    eval' f e = eval'' f e $ mempty
    eval'' f e x = snd . modifyG (\a' e' -> (e', f a' e')) e $ x

instance Manipulatable Expr Expr where
    modifyG f e x =
        let
            (e', x') = f x e
            (e'', x'') = modifyG' f e' (x `mappend` x')
        in
        (e'', x' `mappend` x'')
        where
            modifyG' :: Monoid a => (a -> Expr -> (Expr, a)) -> Expr -> a -> (Expr, a)
            modifyG' f (Lam n e t) x =
                let
                    (e', x') = modifyG f e x
                in
                (Lam n e' t, x')
            modifyG' f (App e1 e2) x =
                let 
                    (e1', x') = modifyG f e1 x
                    (e2', x'') = modifyG f e2 x
                in
                (App e1' e2', x' `mappend` x'')
            modifyG' f (Case e ae t) x =
                let
                    (e', x') = modifyG f e x
                    (ae', x'') = modifyG f ae x
                in
                (Case e' ae' t, x' `mappend` x'')
            modifyG' _ e x = (e, mempty)

instance Manipulatable Type Expr where
    --This is similar to modifyTs, but it acts on all Types in a given Expr
    modifyG f e x = modifyG (f' f) e x
        where
            f' :: Monoid a => (a ->  Type -> (Type, a)) -> a -> Expr -> (Expr, a)
            f' f x (Var n t) =
                let
                    (t', x') = modifyG f t x
                in
                (Var n t', x')
            f' f x (Lam n e t) =
                let
                    (t', x') = modifyG f t x
                in
                (Lam n e t', x')
            f' f x (DCon d) =
                let
                    (d', x') = modifyG f d x
                in
                (DCon d', x')
            f' f x (Case e ae t) =
                let
                    (t', x') = modifyG f t x
                in
                (Case e ae t', x')
            f' f x (Type t) =
                let
                    (t', x') = modifyG f t x
                in
                (Type t', x')
            f' _ _ e = (e, mempty)

instance Manipulatable Expr Type where
    modifyG _ e x = (e, x)

instance Manipulatable Type Type where
    modifyG f t x =
        let
            (t', x') = f x t
            (t'', x'') = modifyT' f t' x'
        in
        (t'', x' `mappend` x'')
        where
            modifyT' :: Monoid a => (a -> Type -> (Type, a)) -> Type -> a -> (Type, a)
            modifyT' f (TyFun t1 t2) x =
                let 
                    (t1', x') = modifyG f t1 x
                    (t2', x'') = modifyG f t2 x
                in
                (TyFun t1' t2', x' `mappend` x'')
            modifyT' f (TyApp t1 t2) x =
                let 
                    (t1', x') = modifyG f t1 x
                    (t2', x'') = modifyG f t2 x
                in
                (TyApp t1' t2', x' `mappend` x'')
            modifyT' f (TyConApp n ts) x =
                let
                    tsx = map (\t' -> modifyG f t' x) ts
                    ts' = map fst tsx
                    x' = mconcat (map snd tsx)
                in
                (TyConApp n ts', x')
            modifyT' f (TyAlg n d) x =
                let
                    (d', x') = modifyG f d x
                in
                (TyAlg n d', x')
            modifyT' f (TyForAll n t) x =
                let
                    (t', x') = modifyG f t x 
                in
                (TyForAll n t', x `mappend` x')
            modifyT' _ t _ = (t, mempty)

instance (Manipulatable e a, Manipulatable e b) => Manipulatable e (a, b) where
    modifyG f (t1, t2) x = 
        let
            (t1', x1') = modifyG f t1 x
            (t2', x2') = modifyG f t2 x
        in
        ((t1', t2'), x1' `mappend` x2')

instance (Manipulatable e a
          , Manipulatable e b
          , Manipulatable e c) => Manipulatable e (a, b, c) where
    modifyG f (t1, t2, t3) x = 
        let
            (t1', x1') = modifyG f t1 x
            (t2', x2') = modifyG f t2 x
            (t3', x3') = modifyG f t3 x
        in
        ((t1', t2', t3'), mconcat[x1', x2', x3'])

instance (Manipulatable e a
          , Manipulatable e b
          , Manipulatable e c
          , Manipulatable e d) => Manipulatable e (a, b, c, d) where
    modifyG f (t1, t2, t3, t4) x = 
        let
            (t1', x1') = modifyG f t1 x
            (t2', x2') = modifyG f t2 x
            (t3', x3') = modifyG f t3 x
            (t4', x4') = modifyG f t4 x
        in
        ((t1', t2', t3', t4'), mconcat [x1', x2', x3', x4'])

instance Manipulatable Expr Alt where
    modifyG f (Alt (dc, n)) x =
        let
            (dc', x') = modifyG f dc x
        in
        (Alt(dc', n), x')

instance Manipulatable Type Alt where
    modifyG f (Alt (dc, n)) x =
        let
            (dc', x') = modifyG f dc x
        in
        (Alt(dc', n), x')

instance Manipulatable Expr DataCon where
    modifyG f dc x = (dc, mempty)

instance Manipulatable Type DataCon where
    modifyG f (DC (n, i, t, tx)) x = 
        let
            (t', x') = modifyG f t x
            (tx', x'') = modifyG f tx x
        in
        (DC (n, i, t', tx'), x' `mappend` x'')


instance Manipulatable e a => Manipulatable e [a] where
    modifyG f e x =
        let
            (e', x') = unzip . map (\e'' -> modifyG f e'' x) $ e
        in
        (e', mconcat x')

instance Manipulatable e v => Manipulatable e (M.Map k v) where
    modifyG f e x =
        let
            res = M.map (\e'' -> modifyG f e'' x) $ e
            e' = M.map fst res
            x' = map snd . M.elems $ res
        in
        (e', mconcat x')

--In order to use a function in Manipulatable, e and m must be
--specifically included in the type signature.  Sometimes, this is
--difficult to ensure for e.  These special cases ensure that only m
--must be included.
modifyGE :: (Manipulatable Expr m, Monoid a) => (a -> Expr -> (Expr, a)) -> m -> a -> (m, a)
modifyGE f e x = modifyG f e x

modifyE :: (Manipulatable Expr m) => (Expr -> Expr) -> m -> m
modifyE f e = modify f e

modifyE' :: (Manipulatable Expr m, Monoid a) => (a -> Expr -> (Expr, a)) -> m -> m
modifyE' f e = modify' f e

modifyE'' :: (Manipulatable Expr m, Monoid a) => (a -> Expr -> (Expr, a)) -> m -> a -> m
modifyE'' f e x = modify'' f e x

modifyGT :: (Manipulatable Type m, Monoid a) => (a -> Type -> (Type, a)) -> m -> a -> (m, a)
modifyGT f e x = modifyG f e x

modifyT :: (Manipulatable Type m) => (Type -> Type) -> m -> m
modifyT f e = modify f e

modifyT' :: (Manipulatable Type m, Monoid a) => (a -> Type -> (Type, a)) -> m -> m
modifyT' f e = modify' f e

modifyT'' :: (Manipulatable Type m, Monoid a) => (a -> Type -> (Type, a)) -> m -> a -> m
modifyT'' f e x = modify'' f e x

evalE :: (Manipulatable Expr m, Monoid a) => (Expr -> a) -> m -> a
evalE f e = eval f e

evalE' :: (Manipulatable Expr m, Monoid a) => (a -> Expr -> a) -> m -> a
evalE' f e = eval' f e

evalE'' :: (Manipulatable Expr m, Monoid a) => (a -> Expr -> a) -> m -> a -> a
evalE'' f e x = eval'' f e x

evalT :: (Manipulatable Type m, Monoid a) => (Type -> a) -> m -> a
evalT f e = eval f e

evalT' :: (Manipulatable Type m, Monoid a) => (a -> Type -> a) -> m -> a
evalT' f e = eval' f e

evalT'' :: (Manipulatable Type m, Monoid a) => (a -> Type -> a) -> m -> a -> a
evalT'' f e x = eval'' f e x

--This is similar to modifyG on types in the typeclass for expression, but it alows access to the expression as well
--This is very similar to that def, might be a neater way to define it?
modifyTsInExpr :: (Manipulatable Expr m, Monoid a) => (Expr -> a -> Type -> (Type, a)) -> m -> a -> (m, a)
modifyTsInExpr f e x = modifyG (f' f) e x
    where
        f' :: Monoid a => (Expr -> a ->  Type -> (Type, a))-> a -> Expr -> (Expr, a)
        f' f x v@(Var n t) =
            let
                (t', x') = modifyG (f v) t x
            in
            (Var n t', x')
        f' f x lam@(Lam n e t) =
            let
                (t', x') = modifyG (f lam) t x
            in
            (Lam n e t', x')
        f' f x e@(DCon d) =
            let
                (d', x') = modifyG (f e) d x
            in
            (DCon d', x')
        f' f x ca@(Case e ae t) =
            let
                (t', x') = modifyG (f ca) t x
            in
            (Case e ae t', x')
        f' f x e@(Type t) =
            let
                (t', x') = modifyG (f e) t x
            in
            (Type t', x')
        f' _ _ e = (e, mempty)

--These are special cases of modifyTsInExpr
modifyTypesInExpr :: Manipulatable Expr m => (Expr -> Type -> Type) -> m -> m
modifyTypesInExpr f t = modifyTypesInExpr' (\e _ t' -> (f e t', ())) t ()

modifyTypesInExpr' :: (Manipulatable Expr m, Monoid a) => (Expr -> a -> Type -> (Type, a)) -> m -> a -> m
modifyTypesInExpr' f t x = fst . modifyTsInExpr f t $ x

evalTypesInExpr ::  (Manipulatable Expr m, Monoid a) => (Expr -> Type -> a) -> m -> a -> a
evalTypesInExpr f e x = evalTypesInExpr' (\e' _ t' -> f e' t') e x

evalTypesInExpr' ::  (Manipulatable Expr m, Monoid a) => (Expr -> a -> Type -> a) -> m -> a -> a
evalTypesInExpr' f e x = snd . modifyTsInExpr (\e' a' t' -> (t', f e' a' t')) e $ x

modifyGOnce :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a)) -> m -> a -> (m, a)
modifyGOnce f e x =
    let
        (e', (b, x')) = modifyG (f' f) e (Mon.All True, x)
    in
    (e', x')
    where
        f' :: Monoid a => (a -> e -> (e, a)) -> (Mon.All, a) -> e -> (e, (Mon.All, a))
        f' f (b, x) e =
            let
                (e', x') = f x e
            in
            if Mon.getAll b then (e', (Mon.All False, x')) else (e, (Mon.All False, mempty))

modifyOnce :: Manipulatable e m => (e -> e) -> m -> m
modifyOnce f e = modifyOnce' (\_ e' -> (f e', ())) e

modifyOnce' :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a)) -> m -> m
modifyOnce' f e = modifyOnce'' f e $ mempty

modifyOnce'' :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a)) -> m -> a -> m
modifyOnce'' f e x = fst . modifyGOnce f e $ x

evalOnce :: (Manipulatable e m, Monoid a) => (e -> a) -> m -> a
evalOnce f e = evalOnce' (\_ e' -> f e') e

evalOnce' :: (Manipulatable e m, Monoid a) => (a -> e -> a) -> m -> a
evalOnce' f e = evalOnce'' f e $ mempty

evalOnce'' :: (Manipulatable e m, Monoid a) => (a -> e -> a) -> m -> a -> a
evalOnce'' f e x = snd . modifyGOnce (\a' e' -> (e', f a' e')) e $ x


--Modifies m with a function (a -> e -> (e, a, b)), but stops if b is false
--modifyGOnce could be rewritten in terms of this?
modifyGUntil :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a, Bool)) -> m -> a -> (m, a)
modifyGUntil f e x =
    let
        (e', (_, x')) = modifyG (f' f) e (Mon.All True, x)
    in
    (e', x')
    where
        f' :: Monoid a => (a -> e -> (e, a, Bool)) -> (Mon.All, a) -> e -> (e, (Mon.All, a))
        f' f (b, x) e =
            let
                (e', x', b') = if Mon.getAll b then f x e else (e, mempty, Mon.getAll b)
            in
            (e', (Mon.All b', x'))

modifyUntil :: Manipulatable e m => (e -> (e, Bool)) -> m -> m
modifyUntil f e = modifyUntil' (\_ e' -> (fst . f $ e', (), snd . f $ e')) e

modifyUntil' :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a, Bool)) -> m -> m
modifyUntil' f e = modifyUntil'' f e $ mempty

modifyUntil'' :: (Manipulatable e m, Monoid a) => (a -> e -> (e, a, Bool)) -> m -> a -> m
modifyUntil'' f e x = fst . modifyGUntil f e $ x

evalUntil :: (Manipulatable e m, Monoid a) => (e -> (a, Bool)) -> m -> a
evalUntil f e = evalUntil' (\_ e' -> f e') e

evalUntil' :: (Manipulatable e m, Monoid a) => (a -> e -> (a, Bool)) -> m -> a
evalUntil' f e = evalUntil'' f e $ mempty

evalUntil'' :: (Manipulatable e m, Monoid a) => (a -> e -> (a, Bool)) -> m -> a -> a
evalUntil'' f e x = snd . modifyGUntil (\a' e' -> (e', fst . f a' $ e', snd . f a' $ e')) e $ x