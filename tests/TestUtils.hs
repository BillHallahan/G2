module TestUtils where

import G2.Internals.Core.Language
import G2.Internals.Core.AST

eqIgT :: Expr -> Expr -> Bool
eqIgT (Var n _) (Var n' _) = n == n'
eqIgT (Const c) (Const c') = c == c'
eqIgT (Prim p _) (Prim p' _) = p == p'
eqIgT (Lam n e _) (Lam n' e' _) = n == n' && e `eqIgT` e'
eqIgT (App e1 e2) (App e1' e2') = e1 `eqIgT` e1' && e2 `eqIgT` e2'
eqIgT (Data (DataCon n _ _ _)) (Data (DataCon n' _ _ _)) = n == n'
eqIgT (Data (PrimCon p)) (Data (PrimCon p')) = p == p'
eqIgT (Type _) (Type _)= True
eqIgT e e' = False
