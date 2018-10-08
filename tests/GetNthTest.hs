{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module GetNthTest where

import G2.Internals.Language
import TestUtils

import Debug.Trace

data CList a = Cons a (CList a) | Nil

data Peano = Succ Peano | Zero

getNth :: CList Integer -> Integer -> Integer
getNth (Cons x _)  0 = x 
getNth (Cons _ xs) n = getNth xs (n - 1)
getNth _      _ = -1

getNthErr :: CList a -> Integer -> Maybe a 
getNthErr (Cons x _)  0 = Just x 
getNthErr (Cons _ xs) n = getNthErr xs (n - 1)
getNthErr _      _ = Nothing

toCList :: Expr -> CList Integer
toCList (App (App (Data (DataCon (Name "Cons" _ _ _) _)) x) y) =
    getInt x Nil $ \x' -> Cons x' (toCList y)
toCList _ = Nil

toCListGen :: Expr -> CList Expr
toCListGen (App (App (Data (DataCon (Name "Cons" _ _ _) _)) e) y) =
    Cons e (toCListGen y)
toCListGen _ = Nil

toCListType :: Expr -> CList Integer
toCListType (App (App (App (Data (DataCon (Name "Cons" _ _ _) _)) (Type _)) x) y) =
    getInt x Nil $ \x' -> Cons x' (toCListType y)
toCListType _ = Nil

toCListGenType :: Expr -> CList Expr
toCListGenType (App (App (App (Data (DataCon (Name "Cons" _ _ _) _)) (Type _)) e) y) =
    Cons e (toCListGenType y)
toCListGenType _ = Nil

cListLength :: CList a -> Integer
cListLength (Cons _ xs) = 1 + cListLength xs
cListLength Nil = 0

getNthTest :: [Expr] -> Bool
getNthTest [cl, i, a] = getIntB i $ \i' -> getIntB a $ \a' -> getNth (toCList cl) i' == a'
getNthTest _ = False

getNthErrTest :: [Expr] -> Bool
getNthErrTest [cl, i, Prim Error _] = getIntB i $ \i' -> getNthErr (toCListType cl) i' == Nothing
getNthErrTest [cl, i, a] = getIntB i $ \i' -> getIntB a $ \a' -> getNthErr (toCListType cl) i' == Just a'
getNthErrTest _ = False

getNthErrGenTest :: [Expr] -> Bool
getNthErrGenTest [cl, i, Prim Error _] = getIntB i $ \i' -> getNthErr (toCListGenType cl) i' == Nothing
getNthErrGenTest [cl, i, e] =
    case getInt i Nothing $ \i' -> getNthErr (toCListGenType cl) i' of
        Just e' -> e' `eqIgT` e
        Nothing -> False
getNthErrGenTest _ = False

getNthErrGenTest' :: [Expr] -> Bool
getNthErrGenTest' [cl, i, Prim Error _] = getIntB i $ \i' -> getNthErr (toCListGenType cl) i' == Nothing
getNthErrGenTest' [cl, i, e] =
    case getInt i Nothing $ \i' -> getNthErr (toCListGenType cl) i' of
        Just e' -> e' `eqIgT` e
        Nothing -> False
getNthErrGenTest' _ = False

getNthErrGenTest2 :: [Expr] -> Bool
getNthErrGenTest2 [cl, i, Prim Error _] = getIntB i $ \i' -> getNthErr (toCListGenType cl) i' == Nothing
getNthErrGenTest2 [cl, i, e] =
    case getInt i Nothing $ \i' -> getNthErr (toCListGenType cl) i' of
        Just e' -> e' `eqIgT` e
        Nothing -> False
getNthErrGenTest2 _ = False

getNthErrGenTest2' :: [Expr] -> Bool
getNthErrGenTest2' [cl, i, Prim Error _] = getIntB i $ \i' -> getNthErr (toCListGenType cl) i' == Nothing
getNthErrGenTest2' [cl, i, e] =
    case getInt i Nothing $ \i' -> getNthErr (toCListGenType cl) i' of
        Just e' -> e' `eqIgT` e
        Nothing -> False
getNthErrGenTest2' _ = False

elimType :: (ASTContainer m Expr) => m -> m
elimType = modifyASTs elimType'

elimType' :: Expr -> Expr
elimType' (App e (Type _)) = e
elimType' e = e

getNthErrors :: [Expr] -> Bool
getNthErrors [cl, App _ (Lit (LitInt i)), Prim Error _] = getNthErr (toCListGen cl) i == Nothing
getNthErrors _ = False

cfmapTest :: [Expr] -> Bool
cfmapTest [_, e, e'] = cListLength (toCListGenType e) == cListLength (toCListGenType e') || isError e'
cfmapTest _ = False
