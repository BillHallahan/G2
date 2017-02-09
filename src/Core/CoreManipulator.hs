module G2.Core.CoreManipulator where

import G2.Core.Language

import qualified Data.List as L

{-
modify f g e x eases mapping over or evaluating an expression in a tree like manner

It allows the passing of information in an arbitrary structure, a, which is initialized
to the value of x.

f x e returns a new expression e', and some value of a, x'.  Each expression, e'', in e',
is then replaced with f e'' x', recursively.
-}

modify ::(a -> Expr -> (Expr, a)) -> (a -> a -> a) -> Expr -> a -> (Expr, a)
modify f g e x = let (e', x') = f x e in modify' f g e' (g x x')
    where 
        modify' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> Expr -> a -> (Expr, a)
        modify' f g (Lam n e t) x =
            let
                (e', x') = modify f g e x
            in
            (Lam n e' t, x')
        modify' f g (App e1 e2) x =
            let 
                (e1', x') = modify f g e1 x
                (e2', x'') = (modify f g e2 x) 
                in (App e1' e2', g x (g x' x''))
        modify' f g (Case e ae t) x =
            let
                (e', x') = modify f g e x
                (ae', x'') = modify'' f g ae x
            in
            (Case e' ae' t,  g x (g x' x''))
        modify' _ _ e x = (e, x) 

        modify'' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> [(Alt, Expr)] -> a -> ([(Alt, Expr)], a)
        modify'' _ _ [] x = ([], x)
        modify'' f g ((a, e):es) x =
            let 
                (e', x') = modify f g e x
                (es', x'') = modify'' f g es x
            in
            ((a, e'):es', g x' x'')

--These are special cases of modify
modifyExpr :: (Expr -> Expr) -> Expr -> Expr
modifyExpr f e = modifyExpr' (\_ e -> (f e, ())) (\_ _ -> ()) e ()

modifyExpr' :: (a -> Expr -> (Expr, a)) -> (a -> a -> a) -> Expr -> a -> Expr
modifyExpr' f g e x = fst . modify f g e $ x

evalExpr :: (Expr -> a) -> (a -> a -> a) -> Expr -> a -> a
evalExpr f g e x = evalExpr' (\_ e-> f e) g e x

evalExpr' :: (a -> Expr -> a) -> (a -> a -> a) -> Expr -> a -> a
evalExpr' f g e x = snd . modify (\a' e -> (e, f a' e)) g e $ x