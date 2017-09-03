-- | Primitive inejction into the environment
module G2.Internals.Translation.PrimInject
    ( primInject
    ) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import qualified Data.List as L
import qualified Data.Map as M

primArity :: Primitive -> Int
primArity Ge = 4
primArity Gt = 4
primArity Eq = 4
primArity Neq = 4
primArity Lt = 4
primArity Le = 4
primArity And = 4
primArity Or = 4
primArity Not = 3
primArity Implies = 2
primArity Plus = 4
primArity Minus = 4
primArity Mult = 4
primArity Div = 4
primArity UNeg = 3

nameToPrim :: Name -> Maybe Primitive
nameToPrim (Name "!" _ _) = Just Not
nameToPrim (Name "-" _ _) = Just UNeg
nameToPrim (Name "&&" _ _) = Just And
nameToPrim (Name "||" _ _) = Just Or
nameToPrim (Name ">=" _ _) = Just Ge
nameToPrim (Name ">" _ _) = Just Gt
nameToPrim (Name "==" _ _) = Just Eq
nameToPrim (Name "/=" _ _) = Just Neq
nameToPrim (Name "<" _ _) = Just Lt
nameToPrim (Name "<=" _ _) = Just Le
nameToPrim (Name "+" _ _) = Just Plus
nameToPrim (Name "-" _ _) = Just Minus
nameToPrim (Name "*" _ _) = Just Mult
nameToPrim (Name "/" _ _) = Just Div
nameToPrim _ = Nothing

nameN :: Int -> Name
nameN i = Name ("a" ++ show i) Nothing i

idN :: Int -> Id
idN i = Id (nameN i) TyBottom

cascadeArity1 :: Primitive -> Expr
cascadeArity1 prim =
    Lam (idN 1)
        (Case (Var (idN 1)) (idN 101) [Alt Default
              (App (Prim prim) (Var (idN 101)))])

cascadeArity2 :: Primitive -> Expr
cascadeArity2 prim =
    Lam (idN 1) (Lam (idN 2)
        (Case (Var (idN 1)) (idN 101) [Alt Default
        (Case (Var (idN 2)) (idN 102) [Alt Default
              (App (App (Prim prim)
                        (Var (idN 101)))
                   (Var (idN 102)))])]))

cascadeArity3 :: Primitive -> Expr
cascadeArity3 prim =
    Lam (idN 1) (Lam (idN 2) (Lam (idN 3)
        (Case (Var (idN 1)) (idN 101) [Alt Default
        (Case (Var (idN 2)) (idN 102) [Alt Default
        (Case (Var (idN 3)) (idN 103) [Alt Default
              (App (App (App (Prim prim)
                             (Var (idN 101)))
                        (Var (idN 102)))
                   (Var (idN 103)))])])])))

cascadeArity4 :: Primitive -> Expr
cascadeArity4 prim =
    Lam (idN 1) (Lam (idN 2) (Lam (idN 3) (Lam (idN 4)
        (Case (Var (idN 1)) (idN 101) [Alt Default
        (Case (Var (idN 2)) (idN 102) [Alt Default
        (Case (Var (idN 3)) (idN 103) [Alt Default
        (Case (Var (idN 4)) (idN 104) [Alt Default
              (App (App (App (App (Prim prim)
                                  (Var (idN 101)))
                             (Var (idN 102)))
                        (Var (idN 103)))
                   (Var (idN 104)))])])])]))))

primCascade :: Primitive -> Expr
primCascade prim = case primArity prim of
    1 -> cascadeArity1 prim
    2 -> cascadeArity2 prim
    3 -> cascadeArity3 prim
    4 -> cascadeArity4 prim
    n -> error $ "primCascade: invalid arity: " ++ show n

primPairs :: Program -> [(Name, Primitive)]
primPairs prog = L.nub $ concatMap flattenPair pairs
  where
    pairs = map (\n -> (n, nameToPrim n)) $ progNames prog

    flattenPair :: (Name, Maybe Primitive) -> [(Name, Primitive)]
    flattenPair (_, Nothing) = []
    flattenPair (n, Just p) = [(n, p)]

pairToBinds :: (Name, Primitive) -> Binds
pairToBinds (name, prim) = [(Id name (typeOf prim), primCascade prim)]

primInject :: Program -> Program
primInject prog = bindss ++ prog
  where
    pairs = primPairs prog
    bindss = map pairToBinds pairs

