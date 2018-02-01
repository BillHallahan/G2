module TestUtils where

import G2.Internals.Language

eqIgT :: Expr -> Expr -> Bool
eqIgT (Var n) (Var n') = eqIgIds n n'
eqIgT (Lit c) (Lit c') = c == c'
eqIgT (Prim p _) (Prim p' _) = p == p'
eqIgT (Lam n e) (Lam n' e') = eqIgIds n n' && e `eqIgT` e'
eqIgT (App e1 e2) (App e1' e2') = e1 `eqIgT` e1' && e2 `eqIgT` e2'
eqIgT (Data (DataCon n _ _)) (Data (DataCon n' _ _)) = eqIgNames n n'
eqIgT (Type _) (Type _)= True
eqIgT _ _ = False


eqIgIds :: Id -> Id -> Bool
eqIgIds (Id n _) (Id n' _) = eqIgNames n n'

eqIgNames :: Name -> Name -> Bool
eqIgNames (Name n m _) (Name n' m' _) = n == n' && m == m'

typeNameIs :: Type -> String -> Bool
typeNameIs (TyConApp (Name n _ _) _) s = n == s
typeNameIs _ _ = False

dcHasName :: String -> Expr -> Bool
dcHasName s (Data (DataCon (Name n _ _) _ _)) = s == n
dcHasName _ _ = False

isBool :: Expr -> Bool
isBool (Data (DataCon _ (TyConApp (Name "Bool" _ _) _) _)) = True
isBool _ = False

dcInAppHasName :: String -> Expr -> Int -> Bool
dcInAppHasName s (Data (DataCon (Name n _ _) _ _)) 0 = s == n
dcInAppHasName s (App a _) n = dcInAppHasName s a (n - 1)
dcInAppHasName _ _ _ = False

buriedDCName :: String -> Expr -> Bool
buriedDCName s (App a _) = buriedDCName s a
buriedDCName s (Data (DataCon (Name n _ _) _ _)) = s == n
buriedDCName _ _ = False

appNthArgIs :: Expr -> (Expr -> Bool) -> Int -> Bool
appNthArgIs a f i = 
    let
        u = unApp a
    in
    case length u > i  of
        True -> f (u !! i)
        False -> False

isInt :: Expr -> (Int -> Bool) -> Bool
isInt (Lit (LitInt x)) f = f x
isInt (App _ (Lit (LitInt x))) f = f x
isInt _ _ = False

appNth :: Expr -> Int -> (Expr -> Bool) -> Bool
appNth e 0 p = p e
appNth (App _ e) i p = appNth e (i - 1) p
appNth _ _ _ = False

isIntT :: Type -> Bool
isIntT (TyConApp (Name "Int" _ _) _) = True
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

getInt :: Expr -> a -> (Int -> a) -> a
getInt (Lit (LitInt x)) _ f = f x
getInt (App _ (Lit (LitInt x))) _ f = f x
getInt _ x _ = x

getIntB :: Expr -> (Int -> Bool) -> Bool
getIntB e = getInt e False

getBoolB :: Expr -> (Bool -> Bool) -> Bool
getBoolB (Data (DataCon (Name n _ _) _ _)) f = f (n == "True")
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
