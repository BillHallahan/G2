{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Execution.PrimitiveEval (evalPrims) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing

import Control.Exception
import Data.Char
import qualified Data.HashMap.Lazy as M
import qualified Data.List as L

evalPrims :: ASTContainer m Expr => TypeEnv -> KnownValues -> m -> m
evalPrims tenv kv = modifyContainedASTs (evalPrims' tenv kv . simplifyCasts)

evalPrims' :: TypeEnv -> KnownValues -> Expr -> Expr
evalPrims' tenv kv a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim' tenv kv [p, evalPrims' tenv kv l]
        [p@(Prim _ _), l1, l2] ->
            evalPrim' tenv kv [p, evalPrims' tenv kv l1, evalPrims' tenv kv l2]
        _ -> App (evalPrims' tenv kv x) (evalPrims' tenv kv y)
evalPrims' tenv kv e = modifyChildren (evalPrims' tenv kv) e

evalPrim' :: TypeEnv -> KnownValues -> [Expr] -> Expr
evalPrim' tenv kv xs
    | [Prim p _, x] <- xs
    , Lit x' <- x =
        case evalPrim1 p x' of
            Just e -> e
            Nothing -> mkApp xs

    | [Prim p _, x, y] <- xs
    , Lit x' <- x
    , Lit y' <- y =
        case evalPrim2 kv p x' y' of
            Just e -> e
            Nothing -> mkApp xs

    | [Prim p _, Type t, dc_e] <- xs, Data dc:_ <- unApp dc_e =
        case evalTypeDCPrim2 tenv p t dc of
            Just e -> e
            Nothing -> mkApp xs

    | [Prim p _, Type t, Lit (LitInt l)] <- xs =
        case evalTypeLitPrim2 tenv p t l of
            Just e -> e
            Nothing -> mkApp xs

    | otherwise = mkApp xs

evalPrim1 :: Primitive -> Lit -> Maybe Expr
evalPrim1 Negate (LitInt x) = Just . Lit $ LitInt (-x)
evalPrim1 Negate (LitFloat x) = Just . Lit $ LitFloat (-x)
evalPrim1 Negate (LitDouble x) = Just . Lit $ LitDouble (-x)
evalPrim1 Abs (LitInt x) = Just . Lit $ LitInt (abs x)
evalPrim1 Abs (LitFloat x) = Just . Lit $ LitFloat (abs x)
evalPrim1 Abs (LitDouble x) = Just . Lit $ LitDouble (abs x)
evalPrim1 SqRt x = evalPrim1Floating (sqrt) x
evalPrim1 IntToFloat (LitInt x) = Just . Lit $ LitFloat (fromIntegral x)
evalPrim1 IntToDouble (LitInt x) = Just . Lit $ LitDouble (fromIntegral x)
evalPrim1 Chr (LitInt x) = Just . Lit $ LitChar (chr $ fromInteger x)
evalPrim1 OrdChar (LitChar x) = Just . Lit $ LitInt (toInteger $ ord x)
evalPrim1 _ _ = Nothing

evalPrim2 :: KnownValues -> Primitive -> Lit -> Lit -> Maybe Expr
evalPrim2 kv Ge x y = evalPrim2NumBool (>=) kv x y
evalPrim2 kv Gt x y = evalPrim2NumBool (>) kv x y
evalPrim2 kv Eq x y = evalPrim2NumBool (==) kv x y
evalPrim2 kv Lt x y = evalPrim2NumBool (<) kv x y
evalPrim2 kv Le x y = evalPrim2NumBool (<=) kv x y
evalPrim2 _ Plus x y = evalPrim2Num (+) x y
evalPrim2 _ Minus x y = evalPrim2Num (-) x y
evalPrim2 _ Mult x y = evalPrim2Num (*) x y
evalPrim2 _  Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ Quot x y = if isZero y then error "Have Quot _ 0" else evalPrim2Integral quot x y
evalPrim2 _ Mod x y = evalPrim2Integral mod x y
evalPrim2 _ _ _ _ = Nothing

evalTypeDCPrim2 :: TypeEnv -> Primitive -> Type -> DataCon -> Maybe Expr
evalTypeDCPrim2 tenv DataToTag t dc =
    case unTyApp t of
        TyCon n _:_ | Just adt <- M.lookup n tenv ->
            let
                dcs = dataCon adt
            in
            fmap (Lit . LitInt . fst) . L.find ((==) dc . snd) $ zip [1..] dcs
        _ -> error "evalTypeDCPrim2: Unsupported Primitive Op"
evalTypeDCPrim2 _ _ _ _ = Nothing

evalTypeLitPrim2 :: TypeEnv -> Primitive -> Type -> Integer -> Maybe Expr
evalTypeLitPrim2 tenv TagToEnum t i =
    case unTyApp t of
        TyCon n _:_ | Just adt <- M.lookup n tenv ->
            let
                dcs = dataCon adt
            in
            maybe (Just $ Prim Error TyBottom) (Just . Data)
                                        $ ith dcs (fromInteger i)
        _ -> error "evalTypeLitPrim2: Unsupported Primitive Op"
evalTypeLitPrim2 _ _ _ _ = Nothing

ith :: [a] -> Integer -> Maybe a
ith (x:_) 0 = Just x
ith (_:xs) n = assert (n > 0) ith xs (n - 1)
ith _ _ = Nothing

isZero :: Lit -> Bool
isZero (LitInt 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumBool :: (forall a . Ord a => a -> a -> Bool) -> KnownValues -> Lit -> Lit -> Maybe Expr
evalPrim2NumBool f kv (LitInt x) (LitInt y) = Just . mkBool kv $ f x y
evalPrim2NumBool f kv (LitFloat x) (LitFloat y) = Just . mkBool kv $ f x y
evalPrim2NumBool f kv (LitDouble x) (LitDouble y) = Just . mkBool kv $ f x y
evalPrim2NumBool _ _ _ _ = Nothing

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
