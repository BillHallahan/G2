module DefuncTest where

import G2.Internals.Language
import TestUtils

-- Defunc1

a :: Expr -> Expr
a = App (Data $ DataCon (Name "A" (Just "Defunc1") 0) (TyConApp (Name "A" (Just "Defunc1") 0) []) [])

dataB :: Expr
dataB = Data $ DataCon (Name "B" (Just "Defunc1") 0) (TyConApp (Name "A" (Just "Defunc1") 0) []) []

b :: Expr -> Expr
b = App (dataB)

add1 :: Expr
add1 = Var (Id (Name "add1" (Just "Defunc1") 0) TyInt) 

multiply2 :: Expr
multiply2 = Var (Id (Name "multiply2" (Just "Defunc1") 0) TyInt) 

defunc1Add1 :: [Expr] -> Bool
defunc1Add1 [x, y] = x `eqIgT` a (add1) &&  y `eqIgT` b (Lit $ LitInt 3)
defunc1Add1 _ = False

defunc1Multiply2 :: [Expr] -> Bool
defunc1Multiply2 [x, y] = x `eqIgT` a (multiply2) && y `eqIgT` b (Lit $ LitInt 4)
defunc1Multiply2 _ = False

defuncB :: [Expr] -> Bool
defuncB [App x _, App y _] = x `eqIgT` dataB && y `eqIgT` dataB
defuncB _ = False

-- Defunc2

add1D2 :: Expr
add1D2 = Var (Id (Name "add1" (Just "Defunc2") 0) TyInt)

sub1D2 :: Expr
sub1D2 = Var (Id (Name "sub1" (Just "Defunc2") 0) TyInt)

squareD2 :: Expr
squareD2 = Var (Id (Name "square" (Just "Defunc2") 0) TyInt) 

iListI :: Expr
iListI = Data $ DataCon (Name "I" (Just "Defunc2") 0) (TyConApp (Name "IList" (Just "Defunc2") 0) []) []

iListNil :: Expr
iListNil = Data $ DataCon (Name "INil" (Just "Defunc2") 0) (TyConApp (Name "IList" (Just "Defunc2") 0) []) []

fListF :: Expr
fListF = Data $ DataCon (Name "F" (Just "Defunc2") 0) (TyConApp (Name "FList" (Just "Defunc2") 0) []) []

fListNil :: Expr
fListNil = Data $ DataCon (Name "FNil" (Just "Defunc2") 0) (TyConApp (Name "FList" (Just "Defunc2") 0) []) []

add1Def :: Int -> Int
add1Def x = x + 1

sub1Def :: Int -> Int
sub1Def x = x - 1

squareDef :: Int -> Int
squareDef x = x * x

defunc2Check :: [Expr] -> Bool
defunc2Check [flist, llist, llist'] = defunc2Check' flist llist llist'
defunc2Check _ = False

defunc2Check' :: Expr -> Expr -> Expr -> Bool
defunc2Check' (App (App _ f) fs) 
              (App (App _ (Lit (LitInt i))) is)
              (App (App _ (Lit (LitInt i'))) is') = defunc2Check'' f i i' && defunc2Check' fs is is'
defunc2Check' _ _ _ = True

defunc2Check'' :: Expr -> Int -> Int -> Bool
defunc2Check'' (Var (Id (Name "add1" _ _) _)) i i' = add1Def i == i'
defunc2Check'' (Var (Id (Name "sub1" _ _) _)) i i' = sub1Def i == i'
defunc2Check'' (Var (Id (Name "square" _ _) _)) i i' = squareDef i == i'
defunc2Check'' _ _ _ = False