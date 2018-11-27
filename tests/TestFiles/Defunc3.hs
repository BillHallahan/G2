module Defunc3 where

data S = S

sIdent :: S -> S
sIdent S = S

s :: (S -> S) -> S
s f = f S
