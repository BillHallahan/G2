module G2.Core.FOL where

import G2.Core.Language

data Term = TVar Name Type
          | TConst Const Type
          | TDataCon DataCon [Term] Type
          | TFun Name [Term] Type
          | TApp Term Term
          | TBAD
          | TUNR
          deriving (Show, Eq)

data Formula = FEq Term Term
             | FAnd Formula Formula
             | FOr Formula Formula
             | FNot Formula
             | FForall Name Formula
             | FExists Name Formula
             deriving (Show, Eq)

