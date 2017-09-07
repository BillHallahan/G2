module G2.Internals.Language.Primitives where

import qualified G2.Internals.Language.ExprEnv as E	
import G2.Internals.Language.Syntax 

import Data.Foldable

-- | Primitive arity.
primArity :: Primitive -> Int
primArity Not = 1
primArity And = 2
primArity Or = 2
primArity Ge = 4
primArity Gt = 4
primArity Eq = 4
primArity Neq = 4
primArity Le = 4
primArity Lt = 4
primArity Plus = 4
primArity Minus = 4
primArity Mult = 4
primArity Div = 4

primStr :: Primitive -> String
primStr Not = "not"
primStr And = "&&"
primStr Or = "||"
primStr Ge = ">="
primStr Gt = ">"
primStr Eq = "=="
primStr Neq = "/="
primStr Le = "<="
primStr Lt = "<"
primStr Plus = "+"
primStr Minus = "-"
primStr Mult = "*"
primStr Div = "/"

strToPrim :: String -> Primitive
strToPrim "not" = Not
strToPrim "&&" = And
strToPrim "||" = Or
strToPrim ">=" = Ge
strToPrim ">" = Gt
strToPrim "==" = Eq
strToPrim "/=" = Neq
strToPrim "<=" = Le
strToPrim "<" = Lt
strToPrim "+" = Plus
strToPrim "-" = Minus
strToPrim "*" = Mult
strToPrim "/" = Div

findPrim :: Primitive -> [(Name, Type)] -> (Name, Type)
findPrim prim [] = error $ "findPrim: not found: " ++ primStr prim
findPrim prim (p@(Name occ _ _, _):ps) =
    if primStr prim == occ then p else findPrim prim ps

mkRawPrim :: [(Name, Type)] -> Name -> Expr
mkRawPrim primtys name@(Name occ _ _) = foldr Lam cases ids
  where
    prim = strToPrim occ
    arity = primArity prim
    ty = snd $ head $ filter (\p -> name == fst p) primtys

    ids = map (\n' -> Id (Name "a" Nothing n') TyBottom) [1..arity]
    binds = map (\n' -> Id (Name "b" Nothing n') TyBottom) [1..arity]

    varIds = map Var ids
    varBinds = map Var binds

    apps = foldl' App (Prim prim ty) varBinds
    cases = foldr (\(i, b) e -> Case i b [Alt Default e]) apps (zip varIds binds)

-- | Primitive lookup helpers

mkPrim :: Primitive -> E.ExprEnv -> Expr
mkPrim p eenv = case E.occLookup (primStr p) (Just "GHC.Classes") eenv of
    Just e -> e
    Nothing -> error $ "Unrecognized prim"

mkGe :: E.ExprEnv -> Expr
mkGe = mkPrim Ge

mkGt :: E.ExprEnv -> Expr
mkGt = mkPrim Gt

mkEq :: E.ExprEnv -> Expr
mkEq = mkPrim Eq

mkNeq :: E.ExprEnv -> Expr
mkNeq = mkPrim Neq

mkLt :: E.ExprEnv -> Expr
mkLt = mkPrim Lt

mkLe :: E.ExprEnv -> Expr
mkLe = mkPrim Le

mkAnd :: E.ExprEnv -> Expr
mkAnd = mkPrim And

mkOr :: E.ExprEnv -> Expr
mkOr = mkPrim Or

mkNot :: E.ExprEnv -> Expr
mkNot = mkPrim Not

mkPlus :: E.ExprEnv -> Expr
mkPlus = mkPrim Plus

mkMinus :: E.ExprEnv -> Expr
mkMinus = mkPrim Minus

mkMult :: E.ExprEnv -> Expr
mkMult = mkPrim Mult

mkDiv :: E.ExprEnv -> Expr
mkDiv = mkPrim Div
