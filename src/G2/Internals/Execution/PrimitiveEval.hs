{-# LANGUAGE Rank2Types #-}

module G2.Internals.Execution.PrimitiveEval (evalPrims) where

import G2.Internals.Language.AST
import G2.Internals.Language.Expr
import G2.Internals.Language.Syntax

evalPrims :: Expr -> Expr
evalPrims a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim [p, evalPrims l]
        [p@(Prim _ _), l1, l2] -> evalPrim [p, evalPrims l1, evalPrims l2]
        [p@(Prim _ _), _, _, l3] -> evalPrim [p, evalPrims l3]
        [p@(Prim _ _), _, _, l1, l2] -> evalPrim [p, evalPrims l1, evalPrims l2]
        _ -> App (evalPrims x) (evalPrims y)
evalPrims e = modifyChildren evalPrims e

evalPrim :: [Expr] -> Expr
evalPrim xs
    | [Prim p _, x] <- xs
    , Lit x' <- getLit x =
        evalPrim1 p x'

    | [Prim p _, x, y] <- xs
    , Lit x' <- getLit x
    , Lit y' <- getLit y =
        evalPrim2 p x' y'

    | [Prim p _, _, _, x, y] <- xs
    , Lit x' <- getLit x
    , Lit y' <- getLit y =
        evalPrim2 p x' y'

    | otherwise = mkApp xs
-- evalPrim [Prim p _, Lit x] = evalPrim1 p x
-- evalPrim [Prim p _, Lit x, Lit y] = evalPrim2 p x y
-- evalPrim [Prim p _, _, _, Lit x, Lit y] = evalPrim2 p x y
-- evalPrim xs = mkApp  (xs)

getLit :: Expr -> Expr
getLit l@(Lit _) = l
getLit (App _ l@(Lit _)) = l
getLit x = x

evalPrim1 :: Primitive -> Lit -> Expr
evalPrim1 Not (LitBool b) = Lit $ LitBool (not b)
evalPrim1 Negate (LitInt x) = Lit $ LitInt (-x)
evalPrim1 Negate (LitFloat x) = Lit $ LitFloat (-x)
evalPrim1 Negate (LitDouble x) = Lit $ LitDouble (-x)
evalPrim1 _ _ = error "Primitive given wrong number of arguments"

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
evalPrim2 Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ _ _ = error "Primitive given wrong number of arguments"

isZero :: Lit -> Bool
isZero (LitInt 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumBool :: (forall a . Ord a => a -> a -> Bool) -> Lit -> Lit -> Expr
evalPrim2NumBool f (LitInt x) (LitInt y) = Lit . LitBool $ f x y
evalPrim2NumBool f (LitFloat x) (LitFloat y) = Lit . LitBool $ f x y
evalPrim2NumBool f (LitDouble x) (LitDouble y) = Lit . LitBool $ f x y
evalPrim2NumBool _ _ _ = error "Primitive given wrong type of arguments"

evalPrim2Bool :: (Bool -> Bool -> Bool) -> Lit -> Lit -> Expr
evalPrim2Bool f (LitBool x) (LitBool y) = Lit . LitBool $ f x y
evalPrim2Bool _ _ _ = error "Primitive given wrong type of arguments"


evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Num f (LitInt x) (LitInt y) = Lit . LitInt $ f x y
evalPrim2Num f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Num f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y
evalPrim2Num _ _ _ = error "Primitive given wrong type of arguments"

evalPrim2Fractional  :: (forall a . Fractional a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Fractional f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Fractional f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y
evalPrim2Fractional _ _ _ = error "Primitive given wrong type of arguments"
