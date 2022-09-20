{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module GetNthTest where

import G2.Language
import TestUtils

data CList a = Cons a (CList a) | Nil

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

getNthErrors :: [Expr] -> Bool
getNthErrors [cl, App _ (Lit (LitInt i)), Prim Error _] = getNthErr (toCListGen cl) i == Nothing
getNthErrors _ = False
