module Typeclass where

data Peano = Zero | Succ Peano

class Number a where
    add :: a -> a -> a
    isZero :: a -> Bool
    -- toInt :: a -> Int

instance Number Peano where
    add Zero p = p
    add (Succ p1) p2 = add p1 (Succ p2)

    isZero Zero = True
    isZero _ = False

    -- toInt (Succ x) = 1 + toInt x
    -- toInt Zero = 0

instance Number Int where
    add = (+)

    isZero 0 = True
    isZero _ = False

    -- toInt x = x

test :: Peano -> Peano
test p = add (Succ p) p

-- diffByTwo :: Int -> Peano -> Bool
-- diffByTwo x y = add x 2 == toInt y || x == toInt (add y (Succ (Succ Zero)))
