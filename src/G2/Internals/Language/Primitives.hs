module G2.Internals.Language.Primitives where

import qualified G2.Internals.Language.ExprEnv as E 
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import Data.Foldable
import Data.Maybe

primStr :: Primitive -> String
primStr Ge = ">="
primStr Gt = ">"
primStr Eq = "=="
primStr Neq = "/="
primStr Lt = "<"
primStr Le = "<="
primStr And = "&&"
primStr Or = "||"
primStr Not = "not"
primStr Implies = "implies"
primStr Plus = "+"
primStr Minus = "-"
primStr Mult = "*"
primStr Div = "/"
primStr Negate = "negate"
primStr Error = "error"
primStr Undefined = "undefined"

strToPrim :: String -> Maybe Primitive
strToPrim "not" = Just Not
strToPrim "&&" = Just And
strToPrim "||" = Just Or
strToPrim ">=" = Just Ge
strToPrim ">" = Just Gt
strToPrim "==" = Just Eq
strToPrim "/=" = Just Neq
strToPrim "<=" = Just Le
strToPrim "<" = Just Lt
strToPrim "+" = Just Plus
strToPrim "-" = Just Minus
strToPrim "*" = Just Mult
strToPrim "/" = Just Div
strToPrim "negate" = Just Negate
strToPrim "error" = Just Error
strToPrim _ = Nothing

findPrim :: Primitive -> [(Name, Type)] -> (Name, Type)
findPrim prim [] = error $ "findPrim: not found: " ++ primStr prim
findPrim prim (p@(Name occ _ _, _):ps) =
    if primStr prim == occ then p else findPrim prim ps

mkRawPrim :: [(Name, Type)] -> Name -> Expr
mkRawPrim primtys name@(Name occ _ _) = 
        case prim of
            Just _ -> foldr Lam cases ids
            Nothing -> Prim Undefined TyBottom
  where
    prim = strToPrim occ

    ty = snd . head $ filter (\p -> name == fst p) primtys
    (forall_ids, ty') = splitTyForAlls ty
    fun_tys = splitTyFuns ty'

    tys = (map typeOf forall_ids) ++ fun_tys

    ids = map (\(i, t) -> Id (Name "a" Nothing i) t) $ zip [1..] (init tys)
    binds = map (\(i, t) -> Id (Name "b" Nothing i) t) $ zip [1..] (init tys)

    varIds = map Var ids
    varBinds = map Var binds

    apps = foldl' App (Prim (fromJust prim) ty) varBinds
    cases = foldr (\(i, b) e -> Case i b [Alt Default e]) apps (zip varIds binds)

-- | Primitive lookup helpers

mkPrim :: Primitive -> E.ExprEnv -> Expr
mkPrim p eenv = case E.occLookup (primStr p) (Just "GHC.Classes") eenv of
    Just e -> Prim p (typeOf e)
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

mkNegate :: E.ExprEnv -> Expr
mkNegate = mkPrim Negate
