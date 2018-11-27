module Strictness1 where

data X = A Int

f :: X
f = A g

g :: Int
g = 3 * 3
