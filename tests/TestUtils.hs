{-# LANGUAGE OverloadedStrings #-}

module TestUtils where

import Data.Monoid
import qualified Data.Text as T

import G2.Config
import G2.Language

mkConfigTest :: Config
mkConfigTest = (mkConfig "/whatever/" [] M.empty)
                    { higherOrderSolver = AllFuncs
                    , timeLimit = 50 }

-- The same thing, because Map is now implicitly included
mkConfigTestWithMap :: Config
mkConfigTestWithMap = mkConfigTest { baseLibs = baseLibs mkConfigTest ++ [mapLib] }


eqIgT :: Expr -> Expr -> Bool
eqIgT (Var n) (Var n') = eqIgIds n n'
eqIgT (Lit c) (Lit c') = c == c'
eqIgT (Prim p _) (Prim p' _) = p == p'
eqIgT (Lam _ n e) (Lam _ n' e') = eqIgIds n n' && e `eqIgT` e'
eqIgT (App e1 e2) (App e1' e2') = e1 `eqIgT` e1' && e2 `eqIgT` e2'
eqIgT (Data (DataCon n _)) (Data (DataCon n' _)) = eqIgNames n n'
eqIgT (Type _) (Type _)= True
eqIgT _ _ = False


eqIgIds :: Id -> Id -> Bool
eqIgIds (Id n _) (Id n' _) = eqIgNames n n'

eqIgNames :: Name -> Name -> Bool
eqIgNames (Name n m _ _) (Name n' m' _ _) = n == n' && m == m'

typeNameIs :: Type -> T.Text -> Bool
typeNameIs (TyCon n _) s = s == nameOcc n
typeNameIs (TyApp t _) s = typeNameIs t s
typeNameIs _ _ = False

dcHasName :: T.Text -> Expr -> Bool
dcHasName s (Data (DataCon n _)) = s == nameOcc n
dcHasName _ _ = False

isBool :: Expr -> Bool
isBool (Data (DataCon _ (TyCon (Name "Bool" _ _ _) _))) = True
isBool _ = False

dcInAppHasName :: T.Text -> Expr -> Int -> Bool
dcInAppHasName s (Data (DataCon n _)) 0 = s == nameOcc n
dcInAppHasName s (App a _) n = dcInAppHasName s a (n - 1)
dcInAppHasName _ _ _ = False

buriedDCName :: T.Text -> Expr -> Bool
buriedDCName s (App a _) = buriedDCName s a
buriedDCName s (Data (DataCon n _)) = s == nameOcc n
buriedDCName _ _ = False

appNthArgIs :: Expr -> (Expr -> Bool) -> Int -> Bool
appNthArgIs a f i = 
    let
        u = unApp a
    in
    case length u > i  of
        True -> f (u !! i)
        False -> False

isInt :: Expr -> (Integer -> Bool) -> Bool
isInt (Lit (LitInt x)) f = f x
isInt (App _ (Lit (LitInt x))) f = f x
isInt _ _ = False

appNth :: Expr -> Int -> (Expr -> Bool) -> Bool
appNth e 0 p = p e
appNth (App _ e) i p = appNth e (i - 1) p
appNth _ _ _ = False

isIntT :: Type -> Bool
isIntT (TyCon (Name "Int" _ _ _) _) = True
isIntT _ = False

isDouble :: Expr -> (Rational -> Bool) -> Bool
isDouble (App _ (Lit (LitDouble x))) f = f x
isDouble _ _ = False

isFloat :: Expr -> (Rational -> Bool) -> Bool
isFloat (Lit (LitFloat x)) f = f x
isFloat (App _ (Lit (LitFloat x))) f = f x
isFloat _ _ = False

inCast :: Expr -> (Expr -> Bool) -> (Coercion -> Bool) -> Bool
inCast (Cast e c) p q = p e && q c
inCast _ _ _ = False

notCast :: Expr -> Bool
notCast (Cast _ _) = False
notCast _ = True

getInt :: Expr -> a -> (Integer -> a) -> a
getInt (Lit (LitInt x)) _ f = f x
getInt (App _ (Lit (LitInt x))) _ f = f x
getInt _ x _ = x

getIntB :: Expr -> (Integer -> Bool) -> Bool
getIntB e = getInt e False

getBoolB :: Expr -> (Bool -> Bool) -> Bool
getBoolB (Data (DataCon n _)) f = f (nameOcc n == "True")
getBoolB _ _ = False

isApp :: Expr -> Bool
isApp (App _ _) = True
isApp _ = False

isError :: Expr -> Bool
isError (Prim Error _) = True
isError _ = False

isTyFun :: Type -> Bool
isTyFun (TyFun _ _) = True
isTyFun _ = False

noUndefined :: Expr -> Bool
noUndefined = getAll . evalASTs noUndefined'

noUndefined' :: Expr -> All
noUndefined' (Prim Undefined _) = All False
noUndefined' _ = All True
