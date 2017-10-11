{-# LANGUAGE Rank2Types #-}

module G2.Internals.Execution.PrimitiveEval (evalPrim) where

import G2.Internals.Language.Syntax

evalPrim :: Primitive -> [Expr] -> Expr
evalPrim p [Lit x] = evalPrim1 p x
evalPrim p [_, _, Lit x, Lit y] = evalPrim2 p x y

evalPrim1 :: Primitive -> Lit -> Expr
evalPrim1 Not (LitBool b) = Lit $ LitBool (not b)

evalPrim1 Negate (LitInt x) = Lit $ LitInt (-x)
evalPrim1 Negate (LitFloat x) = Lit $ LitFloat (-x)
evalPrim1 Negate (LitDouble x) = Lit $ LitDouble (-x)

evalPrim2 :: Primitive -> Lit -> Lit -> Expr
evalPrim2 Ge x y = evalPrim2NumBool (>=) x y
evalPrim2 Gt x y = evalPrim2NumBool (>) x y
evalPrim2 Eq x y = evalPrim2NumBool (==) x y
evalPrim2 Lt x y = evalPrim2NumBool (<) x y
evalPrim2 Le x y = evalPrim2NumBool (<) x y
evalPrim2 And x y = evalPrim2Bool (&&) x y
evalPrim2 Or x y = evalPrim2Bool (||) x y
evalPrim2 Plus x y = evalPrim2Num (+) x y
evalPrim2 Minus x y = evalPrim2Num (-) x y
evalPrim2 Mult x y = evalPrim2Num (*) x y
evalPrim2 Div x y = evalPrim2Fractional (/) x y

evalPrim2NumBool :: (forall a . Ord a => a -> a -> Bool) -> Lit -> Lit -> Expr
evalPrim2NumBool f (LitInt x) (LitInt y) = Lit . LitBool $ f x y
evalPrim2NumBool f (LitFloat x) (LitFloat y) = Lit . LitBool $ f x y
evalPrim2NumBool f (LitDouble x) (LitDouble y) = Lit . LitBool $ f x y

evalPrim2Bool :: (Bool -> Bool -> Bool) -> Lit -> Lit -> Expr
evalPrim2Bool f (LitBool x) (LitBool y) = Lit . LitBool $ f x y

evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Num f (LitInt x) (LitInt y) = Lit . LitInt $ f x y
evalPrim2Num f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Num f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y

evalPrim2Fractional  :: (forall a . Fractional a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Fractional f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Fractional f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y
