module G2.Core.CoreManipulator where

import G2.Core.Language

import qualified Data.List as L

{-
modifyE f g e x eases mapping over or evaluating an expression in a tree like manner

It allows the passing of information in an arbitrary structure, a, which is initialized
to the value of x.

f x e returns a new expression e', and some value of a, x'.  Each expression, e'', in e',
is then replaced with f e'' x', recursively.

modifyT f g e x does the same, except it works on Types
-}

class Manipulatable m where
    modifyE:: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> m -> a -> (m, a)
    modifyExpr :: (Expr -> Expr) -> m -> m
    modifyExpr' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> m -> a -> m

    modifyT :: (a -> Type -> (Type, a)) -> (a -> a -> a) -> m -> a -> (m, a)
    modifyType :: (Type -> Type) -> m -> m
    modifyType' :: (a -> Type -> (Type, a)) -> (a -> a -> a) -> m -> a -> m

    evalExpr :: (Expr -> a) -> (a -> a -> a) -> m -> a -> a
    evalExpr' :: (a -> Expr -> a) -> (a -> a -> a) -> m -> a -> a

    evalType :: (Type -> a) -> (a -> a -> a) -> m -> a -> a
    evalType' :: (a -> Type -> a) -> (a -> a -> a) -> m -> a -> a

    --default implementations
    modifyExpr f e = modifyExpr' (\_ e' -> (f e', ())) (\_ _ -> ()) e ()
    modifyExpr' f g e x = fst . modifyE (\a' e' -> f a' e') g e $ x

    modifyType f t = modifyType' (\_ t' -> (f t', ())) (\_ _ -> ()) t ()
    modifyType' f g t x = fst . modifyT (\a' t' -> f a' t') g t $ x

    evalExpr f g e x = evalExpr' (\_ e' -> f e') g e x
    evalExpr' f g e x = snd . modifyE (\a' e' -> (e', f a' e')) g e $ x

    evalType f g t x = evalType' (\_ t' -> f t') g t x
    evalType' f g t x = snd . modifyT (\a' t' -> (t', f a' t')) g t $ x

instance Manipulatable Expr where
    modifyE f g e x = let (e', x') = f x e in modify' f g e' x'
        where 
            modify' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> Expr -> a -> (Expr, a)
            modify' f g (Lam n e t) x =
                let
                    (e', x') = modifyE f g e x
                in
                (Lam n e' t, g x x')
            modify' f g (App e1 e2) x =
                let 
                    (e1', x') = modifyE f g e1 x
                    (e2', x'') = modifyE f g e2 x
                in
                (App e1' e2', g x (g x' x''))
            modify' f g (Case e ae t) x =
                let
                    (e', x') = modifyE f g e x
                    (ae', x'') = modify'' f g ae x
                in
                (Case e' ae' t, g x (g x' x''))
            modify' _ _ e x = (e, x) 

            modify'' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> [(Alt, Expr)] -> a -> ([(Alt, Expr)], a)
            modify'' _ _ [] x = ([], x)
            modify'' f g ((a, e):es) x =
                let 
                    (e', x') = modifyE f g e x
                    (es', x'') = modify'' f g es x
                in
                ((a, e'):es', g x' x'')

    --This is similar to modifyTs, but it acts on all Types in a given Expr
    modifyT f g e x = modifyE (f' x f g) g e x
        where
            f' :: a -> (a ->  Type -> (Type, a)) -> (a -> a -> a) -> a -> Expr -> (Expr, a)
            f' _ f g x v@(Var n t) =
                let
                    (t', x') = modifyT f g t x
                in
                (Var n t', x')
            f' _ f g x lam@(Lam n e t) =
                let
                    (t', x') = modifyT f g t x
                in
                (Lam n e t', x')
            f' _ f g x e@(DCon d) =
                let
                    (d', x') = modifyTypesDataCon f g d x
                in
                (DCon d', x')
            f' _ f g x ca@(Case e ae t) =
                let
                    (t', x') = modifyT f g t x
                in
                (Case e ae t', x')
            f' _ f g x e@(Type t) =
                let
                    (t', x') = modifyT f g t x
                in
                (Type t', x')
            f' i _ _ _ e = (e, i)
    

instance Manipulatable Type where
    modifyE _ _ e x = (e, x)

    modifyT f g t x = let (t', x') = f x t in modifyT' f g t' x'
        where
            modifyT' :: (a -> Type -> (Type, a)) -> (a -> a -> a) -> Type -> a -> (Type, a)
            modifyT' f g (TyFun t1 t2) x =
                let 
                    (t1', x') = modifyT f g t1 x
                    (t2', x'') = modifyT f g t2 x
                in
                (TyFun t1' t2', g x (g x' x''))
            modifyT' f g (TyApp t1 t2) x =
                let 
                    (t1', x') = modifyT f g t1 x
                    (t2', x'') = modifyT f g t2 x
                in
                (TyApp t1' t2', g x (g x' x''))
            modifyT' f g (TyConApp n ts) x =
                let
                    tsx = map (\t' -> modifyT f g t' x) ts
                    ts' = map fst tsx
                    x' = foldr g x (map snd tsx)
                in
                (TyConApp n ts', x')
            modifyT' f g (TyAlg n d) x =
                let
                    d' = map (\dd -> modifyTypesDataCon f g dd x) d
                    fd = map fst d'
                    x' = foldr g x . map snd $ d'
                in
                (TyAlg n fd, x')
            modifyT' f g (TyForAll n t) x =
                let
                    (t', x') = modifyT f g t x 
                in
                (TyForAll n t', g x x')
            modifyT' _ _ t x = (t, x)

modifyTypesDataCon :: (a -> Type -> (Type, a)) -> (a -> a -> a) -> DataCon -> a -> (DataCon, a)
modifyTypesDataCon f g (n, i, t, tx) x =
    let
        (t', x') = modifyT f g t x
        tx' = map (\tt -> modifyT f g tt x) tx
        ftx = map fst tx'
        x'' = foldr g x' . map snd $ tx'
    in
    ((n, i, t', ftx), x')

--This is similar to modifyTs in the typeclass for expression, but it alllows access to the expression as well
--This is very similar to that def, might be a neater way to define it?
modifyTsInExpr :: (Expr -> a -> Type -> (Type, a)) -> (a -> a -> a) -> Expr -> a -> (Expr, a)
modifyTsInExpr f g e x = modifyE (f' x f g) g e x
    where
        f' :: a -> (Expr -> a ->  Type -> (Type, a)) -> (a -> a -> a) -> a -> Expr -> (Expr, a)
        f' _ f g x v@(Var n t) =
            let
                (t', x') = modifyT (f v) g t x
            in
            (Var n t', x')
        f' _ f g x lam@(Lam n e t) =
            let
                (t', x') = modifyT (f lam) g t x
            in
            (Lam n e t', x')
        f' _ f g x e@(DCon d) =
            let
                (d', x') = modifyTypesDataCon (f e) g d x
            in
            (DCon d', x')
        f' _ f g x ca@(Case e ae t) =
            let
                (t', x') = modifyT (f ca) g t x
            in
            (Case e ae t', x')
        f' _ f g x e@(Type t) =
            let
                (t', x') = modifyT (f e) g t x
            in
            (Type t', x')
        f' i _ _ _ e = (e, i)

-- --These are special cases of modifyTsInExpr
modifyTypesInExpr :: (Type -> Type) -> Expr -> Expr
modifyTypesInExpr f e = modifyTypesInExpr' (\_ t' -> f t') e

modifyTypesInExpr' :: (Expr -> Type -> Type) -> Expr -> Expr
modifyTypesInExpr' f t = modifyTypesInExpr'' (\e _ t' -> (f e t', ())) (\_ _ -> ()) t ()

modifyTypesInExpr'' :: (Expr -> a -> Type -> (Type, a)) -> (a -> a -> a) -> Expr -> a -> Expr
modifyTypesInExpr'' f g t x = fst . modifyTsInExpr f g t $ x

evalTypesInExpr :: (Type -> a) -> (a -> a -> a) -> Expr -> a -> a
evalTypesInExpr f g e x = evalTypesInExpr' (\_ t' -> f t') g e x

evalTypesInExpr' ::  (Expr -> Type -> a) -> (a -> a -> a) -> Expr -> a -> a
evalTypesInExpr' f g e x = evalTypesInExpr'' (\e' _ t' -> f e' t') g e x

evalTypesInExpr'' ::  (Expr -> a -> Type -> a) -> (a -> a -> a) -> Expr -> a -> a
evalTypesInExpr'' f g e x = snd . modifyTsInExpr (\e' a' t' -> (t', f e' a' t')) g e $ x