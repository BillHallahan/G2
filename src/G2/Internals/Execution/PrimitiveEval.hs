{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Execution.PrimitiveEval (evalPrims) where

import G2.Internals.Language.AST
import G2.Internals.Language.Expr
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax

evalPrims :: ASTContainer m Expr => KnownValues -> TypeEnv -> m -> m
evalPrims kv tenv = modifyContainedASTs (evalPrims' kv tenv . simplifyCasts)

evalPrims' :: KnownValues -> TypeEnv -> Expr -> Expr
evalPrims' kv tenv a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim kv tenv [p, evalPrims' kv tenv l]
        [p@(Prim _ _), l1, l2] -> evalPrim kv tenv [p, evalPrims' kv tenv l1, evalPrims' kv tenv l2]
        [p@(Prim _ _), _, _, l3] -> evalPrim kv tenv [p, evalPrims' kv tenv l3]
        [p@(Prim _ _), _, _, l1, l2] -> evalPrim kv tenv [p, evalPrims' kv tenv l1, evalPrims' kv tenv l2]
        _ -> App (evalPrims' kv tenv x) (evalPrims' kv tenv y)
evalPrims' kv tenv e = modifyChildren (evalPrims' kv tenv) e

evalPrim :: KnownValues -> TypeEnv -> [Expr] -> Expr
evalPrim kv tenv xs
    | [Prim p _, x] <- xs
    , Lit x' <- getLit x =
        evalPrim1 p x'

    | [Prim p _, x, y] <- xs
    , Lit x' <- getLit x
    , Lit y' <- getLit y =
        evalPrim2 kv tenv p x' y'

    | [Prim p _, _, _, x, y] <- xs
    , Lit x' <- getLit x
    , Lit y' <- getLit y =
        evalPrim2 kv tenv p x' y'

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
evalPrim1 Negate (LitInt x) = Lit $ LitInt (-x)
evalPrim1 Negate (LitFloat x) = Lit $ LitFloat (-x)
evalPrim1 Negate (LitDouble x) = Lit $ LitDouble (-x)
evalPrim1 SqRt x = evalPrim1Floating (sqrt) x
evalPrim1 IntToFloat (LitInt x) = Lit $ LitFloat (fromIntegral x)
evalPrim1 IntToDouble (LitInt x) = Lit $ LitDouble (fromIntegral x)
evalPrim1 p _ = error $ "Primitive given wrong number of arguments (1) " ++ show p

evalPrim2 :: KnownValues -> TypeEnv -> Primitive -> Lit -> Lit -> Expr
evalPrim2 kv tenv Ge x y = evalPrim2NumBool (>=) kv tenv x y
evalPrim2 kv tenv Gt x y = evalPrim2NumBool (>) kv tenv x y
evalPrim2 kv tenv Eq x y = evalPrim2NumBool (==) kv tenv x y
evalPrim2 kv tenv Lt x y = evalPrim2NumBool (<) kv tenv x y
evalPrim2 kv tenv Le x y = evalPrim2NumBool (<) kv tenv x y
evalPrim2 _ _ Plus x y = evalPrim2Num (+) x y
evalPrim2 _ _ Minus x y = evalPrim2Num (-) x y
evalPrim2 _ _ Mult x y = evalPrim2Num (*) x y
evalPrim2 _ _ Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ _ Quot x y = if isZero y then error "Have Quot _ 0" else evalPrim2Integral quot x y
evalPrim2 _ _ Mod x y = evalPrim2Integral (mod) x y
evalPrim2 _ _ p _ _ = error $ "Primitive given wrong number of arguments (2) " ++ show p

isZero :: Lit -> Bool
isZero (LitInt 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumBool :: (forall a . Ord a => a -> a -> Bool) -> KnownValues -> TypeEnv -> Lit -> Lit -> Expr
evalPrim2NumBool f kv tenv (LitInt x) (LitInt y) = mkBool kv tenv $ f x y
evalPrim2NumBool f kv tenv (LitFloat x) (LitFloat y) = mkBool kv tenv $ f x y
evalPrim2NumBool f kv tenv (LitDouble x) (LitDouble y) = mkBool kv tenv $ f x y
evalPrim2NumBool _ _ _ _ _ = error "Bool: Primitive given wrong type of arguments"

evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Num f (LitInt x) (LitInt y) = Lit . LitInt $ f x y
evalPrim2Num f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Num f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y
evalPrim2Num _ _ _ = error "Num: Primitive given wrong type of arguments"

evalPrim2Fractional  :: (forall a . Fractional a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Fractional f (LitFloat x) (LitFloat y) = Lit . LitFloat $ f x y
evalPrim2Fractional f (LitDouble x) (LitDouble y) = Lit . LitDouble $ f x y
evalPrim2Fractional _ _ _ = error "Fractional: Primitive given wrong type of arguments"

evalPrim2Integral :: (forall a . Integral a => a -> a -> a) -> Lit -> Lit -> Expr
evalPrim2Integral f (LitInt x) (LitInt y) = Lit . LitInt $ f x y
evalPrim2Integral _ _ _ = error "Integral: Primitive given wrong type of arguments"

evalPrim1Floating :: (forall a . Floating a => a -> a) -> Lit -> Expr
evalPrim1Floating f (LitFloat x) = Lit . LitFloat . toRational $ f (fromRational x :: Double)
evalPrim1Floating f (LitDouble x)  = Lit . LitDouble . toRational $ f (fromRational x :: Double)
evalPrim1Floating _ _ = error "Floating: Primitive given wrong type of arguments"