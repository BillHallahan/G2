{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Execution.PrimitiveEval (evalPrims, evalPrim) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax

evalPrims :: ASTContainer m Expr => KnownValues -> TypeEnv -> m -> m
evalPrims kv tenv = modifyContainedASTs (evalPrims' kv tenv . simplifyCasts)

evalPrim :: KnownValues -> TypeEnv -> Expr -> Expr
evalPrim kv tenv a@(App _ _) =
    case unApp a of
        [p@(Prim _ _), l@(Lit _)] -> evalPrim' kv tenv [p, l]
        [p@(Prim _ _), l1@(Lit _), l2@(Lit _)] -> evalPrim' kv tenv [p, l1, l2]
        _ -> a
evalPrim _ _ e = e


evalPrims' :: KnownValues -> TypeEnv -> Expr -> Expr
evalPrims' kv tenv a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim' kv tenv [p, evalPrims' kv tenv l]
        [p@(Prim _ _), l1, l2] -> evalPrim' kv tenv [p, evalPrims' kv tenv l1, evalPrims' kv tenv l2]
        _ -> App (evalPrims' kv tenv x) (evalPrims' kv tenv y)
evalPrims' kv tenv e = modifyChildren (evalPrims' kv tenv) e

evalPrim' :: KnownValues -> TypeEnv -> [Expr] -> Expr
evalPrim' kv tenv xs
    | [Prim p _, x] <- xs
    , Lit x' <- getLit x =
        case evalPrim1 p x' of
            Just e -> e
            Nothing -> mkApp xs

    | [Prim p _, x, y] <- xs
    , Lit x' <- getLit x
    , Lit y' <- getLit y =
        case evalPrim2 kv tenv p x' y' of
            Just e -> e
            Nothing -> mkApp xs

    | otherwise = mkApp xs

getLit :: Expr -> Expr
getLit l@(Lit _) = l
getLit x = x

evalPrim1 :: Primitive -> Lit -> Maybe Expr
evalPrim1 Negate (LitInt x) = Just . Lit $ LitInt (-x)
evalPrim1 Negate (LitFloat x) = Just . Lit $ LitFloat (-x)
evalPrim1 Negate (LitDouble x) = Just . Lit $ LitDouble (-x)
evalPrim1 SqRt x = evalPrim1Floating (sqrt) x
evalPrim1 IntToFloat (LitInt x) = Just . Lit $ LitFloat (fromIntegral x)
evalPrim1 IntToDouble (LitInt x) = Just . Lit $ LitDouble (fromIntegral x)
evalPrim1 _ _ = Nothing

evalPrim2 :: KnownValues -> TypeEnv -> Primitive -> Lit -> Lit -> Maybe Expr
evalPrim2 kv tenv Ge x y = evalPrim2NumBool (>=) kv tenv x y
evalPrim2 kv tenv Gt x y = evalPrim2NumBool (>) kv tenv x y
evalPrim2 kv tenv Eq x y = evalPrim2NumBool (==) kv tenv x y
evalPrim2 kv tenv Lt x y = evalPrim2NumBool (<) kv tenv x y
evalPrim2 kv tenv Le x y = evalPrim2NumBool (<=) kv tenv x y
evalPrim2 _ _ Plus x y = evalPrim2Num (+) x y
evalPrim2 _ _ Minus x y = evalPrim2Num (-) x y
evalPrim2 _ _ Mult x y = evalPrim2Num (*) x y
evalPrim2 _ _ Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ _ Quot x y = if isZero y then error "Have Quot _ 0" else evalPrim2Integral quot x y
evalPrim2 _ _ Mod x y = evalPrim2Integral (mod) x y
evalPrim2 _ _ _ _ _ = Nothing

isZero :: Lit -> Bool
isZero (LitInt 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumBool :: (forall a . Ord a => a -> a -> Bool) -> KnownValues -> TypeEnv -> Lit -> Lit -> Maybe Expr
evalPrim2NumBool f kv tenv (LitInt x) (LitInt y) = Just . mkBool kv tenv $ f x y
evalPrim2NumBool f kv tenv (LitFloat x) (LitFloat y) = Just . mkBool kv tenv $ f x y
evalPrim2NumBool f kv tenv (LitDouble x) (LitDouble y) = Just . mkBool kv tenv $ f x y
evalPrim2NumBool _ _ _ _ _ = Nothing

evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Num f (LitInt x) (LitInt y) = Just . Lit . LitInt $ f x y
evalPrim2Num f (LitFloat x) (LitFloat y) = Just . Lit . LitFloat $ f x y
evalPrim2Num f (LitDouble x) (LitDouble y) = Just . Lit . LitDouble $ f x y
evalPrim2Num _ _ _ = Nothing

evalPrim2Fractional  :: (forall a . Fractional a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Fractional f (LitFloat x) (LitFloat y) = Just . Lit . LitFloat $ f x y
evalPrim2Fractional f (LitDouble x) (LitDouble y) = Just . Lit . LitDouble $ f x y
evalPrim2Fractional _ _ _ = Nothing

evalPrim2Integral :: (forall a . Integral a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Integral f (LitInt x) (LitInt y) = Just . Lit . LitInt $ f x y
evalPrim2Integral _ _ _ = Nothing

evalPrim1Floating :: (forall a . Floating a => a -> a) -> Lit -> Maybe Expr
evalPrim1Floating f (LitFloat x) = Just . Lit . LitFloat . toRational $ f (fromRational x :: Double)
evalPrim1Floating f (LitDouble x)  = Just . Lit . LitDouble . toRational $ f (fromRational x :: Double)
evalPrim1Floating _ _ = Nothing
