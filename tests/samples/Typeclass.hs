module Typeclass where

data Peano = Zero | Succ Peano

class Number a where
    add :: a -> a -> a
    isZero :: a -> Bool


instance Number Peano where
    add Zero p = p
    add (Succ p1) p2 = add p1 (Succ p2)

    isZero Zero = True
    isZero _ = False

main = undefined

