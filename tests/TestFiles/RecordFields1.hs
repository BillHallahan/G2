module RecordFields1 where

data Y = A | B | C

data X = X { count :: Int
           , alg :: Y }

fCall :: Int
fCall = f (X { count = 34
             , alg = A})

f :: X -> Int
f x = count x + 1

g :: X -> X
g x@(X {alg = A}) = x {alg = B}
g x@(X {alg = B}) = x {alg = C}
g x@(X {alg = C}) = x {alg = A}
