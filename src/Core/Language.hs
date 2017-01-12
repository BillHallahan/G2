module G2.Core.Language where

import qualified Data.Map as M

type State = (Env, Expr, PC)

type PC = [(Expr, Alt)]

type Env = M.Map Name Expr

type Name = String

data Expr = Var Name Type
          | Const Const Type
          | Lam Name Expr Type
          | App Expr Expr
          | DCon DataCon
          | Case Expr [(Alt, Expr)] Type
          | BAD
          | UNR
          deriving (Show, Eq)

data Const = CInt Int
           | CReal Rational
           | CString String
           | CChar Char
           deriving (Show, Eq)

type DataCon = (Name, Int, Type, [Type])

data Type = TyVar Name
          | TyInt | TyReal | TyBool | TyString | TyChar
          | TyFun Type Type
          | TyConApp Name [Type]
          | TyAlg Name [DataCon]
          | TyBottom
          deriving (Show, Eq)

type Alt = (DataCon, [Name])

