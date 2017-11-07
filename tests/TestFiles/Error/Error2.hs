module Error2 where

data X = X | Y X X

f :: X
f = Y X (error "Error")