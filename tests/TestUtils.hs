module TestUtils where

import G2.Internals.Language

eqIgT :: Expr -> Expr -> Bool
eqIgT (Var n) (Var n') = eqIgIds n n'
eqIgT (Lit c) (Lit c') = c == c'
eqIgT (Prim p _) (Prim p' _) = p == p'
eqIgT (Lam n e) (Lam n' e') = eqIgIds n n' && e `eqIgT` e'
eqIgT (App e1 e2) (App e1' e2') = e1 `eqIgT` e1' && e2 `eqIgT` e2'
eqIgT (Data (DataCon n _ _)) (Data (DataCon n' _ _)) = eqIgNames n n'
eqIgT (Data (PrimCon p)) (Data (PrimCon p')) = p == p'
eqIgT (Type _) (Type _)= True
eqIgT _ _ = False


eqIgIds :: Id -> Id -> Bool
eqIgIds (Id n _) (Id n' _) = eqIgNames n n'

eqIgNames :: Name -> Name -> Bool
eqIgNames (Name n m _) (Name n' m' _) = n == n' && m == m'

dcHasName :: String -> Expr -> Bool
dcHasName s (Data (DataCon (Name n _ _) _ _)) = s == n
dcHasName _ _ = False

isBool :: Expr -> Bool
isBool (Lit (LitBool _)) = True
isBool _ = False

dcInAppHasName :: String -> Expr -> Int -> Bool
dcInAppHasName s (Data (DataCon (Name n _ _) _ _)) 0 = s == n
dcInAppHasName s (App a _) n = dcInAppHasName s a (n - 1)
dcInAppHasName _ _ _ = False

appNthArgIs :: Expr -> (Expr -> Bool) -> Int -> Bool
appNthArgIs a f i = 
    let
        u = unApp a
    in
    case length u > i  of
        True -> f (u !! i)
        False -> False

isInt :: Expr -> Bool
isInt (Lit (LitInt _)) = True
isInt _ = False