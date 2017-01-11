module G2.Core.Language where

import qualified Data.Map as M

type EEnv = M.Map Name Expr

type TEnv = M.Map Name [DataCon]

type Name = String

data Expr = Var Name
          | Const Const
          | Lam Name Expr
          | App Expr Expr
          | DCon DataCon
          | Case Expr [(Alt, Expr)]
          deriving (Show, Eq)

data Const = CInt Int
           | CReal Rational
           | CString String
           | CChar Char
           deriving (Show, Eq)

type DataCon = (Name, Int, [Type])

data Type = TyVar Name
          | TyInt
          | TyBool
          | TyReal
          | TyFun Type Type
          | TyConApp Name [Type]
          deriving (Show, Eq)

type Alt = (DataCon, [Name])

