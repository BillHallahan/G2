-- We want to avoid splitting too much, when it's not needed.

module Expr where

data Expr = Var Int
          | Data Int
          | Lam Int Expr
          | BinOp Bin Expr Expr
          | UnOp Un Expr
          | Const Const

data Bin = Add | Sub | Mul

data Un = Neg

data Const = CTrue | CFalse

leadingLams :: Expr -> [Int]
leadingLams (Lam i e) = i:leadingLams e
leadingLams _ = []

varSub :: Int -> Int -> Expr -> Expr
varSub old new v@(Var x) = if x == old then Var new else v
varSub old new (Lam i e) = Lam (if i == old then new else i) (varSub old new e)
varSub old new (BinOp b e e') = BinOp b (varSub old new e) (varSub old new e')
varSub old new (UnOp u e) = UnOp u (varSub old new e)
varSub _ _ e = e
