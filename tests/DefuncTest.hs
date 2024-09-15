{-# LANGUAGE OverloadedStrings #-}

module DefuncTest where

import G2.Language
import TestUtils

-- Defunc1

a :: Expr -> Expr
a = App (Data $ DataCon (Name "A" (Just "Defunc1") 0 Nothing) (TyCon (Name "A" (Just "Defunc1") 0 Nothing) TYPE) [] [])

dataB :: Expr
dataB = Data $ DataCon (Name "B" (Just "Defunc1") 0 Nothing) (TyCon (Name "A" (Just "Defunc1") 0 Nothing) TYPE) [] []

add1 :: Expr
add1 = Var (Id (Name "add1" (Just "Defunc1") 0 Nothing) tyIntS) 

multiply2 :: Expr
multiply2 = Var (Id (Name "multiply2" (Just "Defunc1") 0 Nothing) tyIntS) 

defunc1Add1 :: [Expr] -> Bool
defunc1Add1 [x, (App b (App _ y))] = x `eqIgT` a (add1) && b `eqIgT` dataB &&  y `eqIgT` (Lit $ LitInt 3)
defunc1Add1 _ = False

defunc1Multiply2 :: [Expr] -> Bool
defunc1Multiply2 [x, (App b (App _ y))] = x `eqIgT` a (multiply2) && b `eqIgT` dataB && y `eqIgT` (Lit $ LitInt 4)
defunc1Multiply2 _ = False

defuncB :: [Expr] -> Bool
defuncB [App x _, App y _] = x `eqIgT` dataB && y `eqIgT` dataB
defuncB _ = False

-- Defunc2

tyIntS :: Type
tyIntS = TyCon (Name "Int" Nothing 0 Nothing) TYPE
