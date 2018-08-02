{-# LANGUAGE OverloadedStrings #-}

module DefuncTest where

import G2.Internals.Language
import TestUtils

-- Defunc1

a :: Expr -> Expr
a = App (Data $ DataCon (Name "A" (Just "Defunc1") 0 Nothing) (TyConApp (Name "A" (Just "Defunc1") 0 Nothing) []))

dataB :: Expr
dataB = Data $ DataCon (Name "B" (Just "Defunc1") 0 Nothing) (TyConApp (Name "A" (Just "Defunc1") 0 Nothing) [])

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

add1D2 :: Expr
add1D2 = Var (Id (Name "add1" (Just "Defunc2") 0 Nothing) tyIntS)

sub1D2 :: Expr
sub1D2 = Var (Id (Name "sub1" (Just "Defunc2") 0 Nothing) tyIntS)

squareD2 :: Expr
squareD2 = Var (Id (Name "square" (Just "Defunc2") 0 Nothing) tyIntS) 

iListI :: Expr
iListI = Data $ DataCon (Name "I" (Just "Defunc2") 0 Nothing) (TyConApp (Name "IList" (Just "Defunc2") 0 Nothing) [])

iListNil :: Expr
iListNil = Data $ DataCon (Name "INil" (Just "Defunc2") 0 Nothing) (TyConApp (Name "IList" (Just "Defunc2") 0 Nothing) [])

fListF :: Expr
fListF = Data $ DataCon (Name "F" (Just "Defunc2") 0 Nothing) (TyConApp (Name "FList" (Just "Defunc2") 0 Nothing) [])

fListNil :: Expr
fListNil = Data $ DataCon (Name "FNil" (Just "Defunc2") 0 Nothing) (TyConApp (Name "FList" (Just "Defunc2") 0 Nothing) [])

add1Def :: Integer -> Integer
add1Def x = x + 1

sub1Def :: Integer -> Integer
sub1Def x = x - 1

squareDef :: Integer -> Integer
squareDef x = x * x

defunc2Check :: [Expr] -> Bool
defunc2Check [flist, llist, llist'] = defunc2Check' flist llist llist'
defunc2Check _ = False

defunc2Check' :: Expr -> Expr -> Expr -> Bool
defunc2Check' (App (App _ f) fs) 
              (App (App _ (Lit (LitInt i))) is)
              (App (App _ (Lit (LitInt i'))) is') = defunc2Check'' f i i' && defunc2Check' fs is is'
defunc2Check' _ _ _ = True

defunc2Check'' :: Expr -> Integer -> Integer -> Bool
defunc2Check'' (Var (Id (Name "add1" _ _ _) _)) i i' = add1Def i == i'
defunc2Check'' (Var (Id (Name "sub1" _ _ _) _)) i i' = sub1Def i == i'
defunc2Check'' (Var (Id (Name "square" _ _ _) _)) i i' = squareDef i == i'
defunc2Check'' _ _ _ = False

tyIntS :: Type
tyIntS = TyConApp (Name "Int" Nothing 0 Nothing) []