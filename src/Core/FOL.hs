module G2.Core.FOL where

import G2.Core.Language

data Term = TVar Name
          | TDataCon DataCon [Term]
          | TSelK DataCon Int
          | TFun Name [Term]
          | BAD
          | TUNR
          deriving (Show, Eq)

data Formula = FEq Term Term
             | FAnd Formula Formula
             | FOr Formula Formula
             | FNot Formula
             | FForall Name Formula
             | FExists Name Formula
             deriving (Show, Eq)

