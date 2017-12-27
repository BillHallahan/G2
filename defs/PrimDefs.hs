{-# LANGUAGE MagicHash #-}
module PrimDefs where

import Prelude (Int, Integer, Float, Double, Rational, Bool, Char)
import GHC.Prim
import GHC.Types

class Num a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    abs :: a -> a
    signum :: a -> a
    fromInteger :: Integer -> a
    negate :: a -> a

class Fractional a where
    (/) :: a -> a -> a
    recip :: a -> a
    fromRational :: Rational -> a

class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool

class Ord a where
    compare :: a -- This is not the real type!
    (<=) :: a -> a -> Bool
    (<) :: a -> a -> Bool
    (>) :: a -> a -> Bool
    (>=) :: a -> a -> Bool
    max :: a -> a -> a
    min :: a -> a -> a

instance Num Int where
    (+) (I# x) (I# y) = I# (x .+# y)
    (*) (I# x) (I# y) = I# (x .*# y)
    abs n = if n >= 0 then n else negate n
    signum n | n < 0 = negate 1
             | n == 0 = 0
             | n > 0 = 1
    fromInteger = undefined
    (-) (I# x) (I# y) = I# (x .-# y)
    negate (I# x) = I# (negateInt## x)

(.+#) :: Int# -> Int# -> Int#
(.+#) = (.+#)

(.*#) :: Int# -> Int# -> Int#
(.*#) = (.*#)

(.-#) :: Int# -> Int# -> Int#
(.-#) = (.-#)

negateInt## :: Int# -> Int#
negateInt## = negateInt##

instance Num Double where
    (+) (D# x) (D# y) = D# (x .+## y)
    (*) (D# x) (D# y) = D# (x .*##y )
    abs n = if n >= 0 then n else negate n
    signum n | n < 0 = negate 1
             | n == 0 = 0
             | n > 0 = 1
    fromInteger = undefined
    (-) (D# x) (D# y) = D# (x .-## y)
    negate (D# x) = D# (negateDouble## x)

(.+##) :: Double# -> Double# -> Double#
(.+##) = (.+##)

(.*##) :: Double# -> Double# -> Double#
(.*##) = (.*##)

(.-##) :: Double# -> Double# -> Double#
(.-##) = (.-##)

negateDouble## :: Double# -> Double#
negateDouble## = negateDouble##

instance Num Float where
    (+) (F# x) (F# y) = F# (x `plusFloat##` y)
    (*) (F# x) (F# y) = F# (x `timesFloat##` y)
    abs n = if n >= 0 then n else negate n
    signum n | n < 0 = negate 1
             | n == 0 = 0
             | n > 0 = 1
    fromInteger = undefined
    (-) (F# x) (F# y) = F# (x `minusFloat##` y)
    negate (F# x) = F# (negateFloat## x)

plusFloat## :: Float# -> Float# -> Float#
plusFloat## = plusFloat##

timesFloat##  :: Float# -> Float# -> Float#
timesFloat## = timesFloat##

minusFloat## :: Float# -> Float# -> Float#
minusFloat## = minusFloat##

negateFloat## :: Float# -> Float#
negateFloat## = negateFloat##

instance Fractional Double where
    (/) (D# x) (D# y) = D# (x ./## y)
    recip = undefined
    fromRational = undefined

(./##) :: Double# -> Double# -> Double#
(./##) = (./##)

instance Fractional Float where
    (/) (F# x) (F# y) = F# (x `divFloat##` y)
    recip = undefined
    fromRational = undefined

divFloat## :: Float# -> Float# -> Float#
divFloat## = divFloat##

instance Eq Int where
    (==) (I# x) (I# y) = x .==# y
    (/=) (I# x) (I# y) = x ./=# y

(.==#) :: Int# -> Int# -> Bool
(.==#) = (.==#)

(./=#) :: Int# -> Int# -> Bool
(./=#) = (./=#)

instance Eq Double where
    (==) (D# x) (D# y) = x .==## y
    (/=) (D# x) (D# y) = x ./=## y

(.==##) :: Double# -> Double# -> Bool
(.==##) = (.==##)

(./=##) :: Double# -> Double# -> Bool
(./=##) = (./=##)

instance Eq Float where
    (==) (F# x) (F# y) = x `eqFloat'#` y
    (/=) (F# x) (F# y) = x `neqFloat'#` y

eqFloat'# :: Float# -> Float# -> Bool
eqFloat'# = eqFloat'#

neqFloat'# :: Float# -> Float# -> Bool
neqFloat'# = neqFloat'#

instance Ord Int where
    compare = undefined
    (<=) (I# x) (I# y) = x .<=# y
    (<) (I# x) (I# y) = x .<# y
    (>) (I# x) (I# y) = x .># y
    (>=) (I# x) (I# y) = x .>=# y
    max = undefined
    min = undefined

(.<=#) :: Int# -> Int# -> Bool
(.<=#) = (.<=#)

(.<#) :: Int# -> Int# -> Bool
(.<#) = (.<#)

(.>#) :: Int# -> Int# -> Bool
(.>#) = (.>#)

(.>=#) :: Int# -> Int# -> Bool
(.>=#) = (.>=#)

instance Ord Double where
    compare = undefined
    (<=) (D# x) (D# y) = x .<=## y
    (<) (D# x) (D# y) = x .<## y
    (>) (D# x) (D# y) = x .>## y
    (>=) (D# x) (D# y) = x .>=## y
    max = undefined
    min = undefined

(.<=##) :: Double# -> Double# -> Bool
(.<=##) = (.<=##)

(.<##) :: Double# -> Double# -> Bool
(.<##) = (.<##)

(.>##) :: Double# -> Double# -> Bool
(.>##) = (.>##)

(.>=##) :: Double# -> Double# -> Bool
(.>=##) = (.>=##)

instance Ord Float where
    compare = undefined
    (<=) (F# x) (F# y) = x `leFloat'#` y
    (<) (F# x) (F# y) = x `ltFloat'#` y
    (>) (F# x) (F# y) = x `gtFloat'#` y
    (>=) (F# x) (F# y) = x `geFloat'#` y
    max = undefined
    min = undefined

leFloat'# :: Float# -> Float# -> Bool
leFloat'# = leFloat'#

ltFloat'# :: Float# -> Float# -> Bool
ltFloat'# = ltFloat'#

gtFloat'# :: Float# -> Float# -> Bool
gtFloat'# = gtFloat'#

geFloat'# :: Float# -> Float# -> Bool
geFloat'# = geFloat'#

(&&) :: Bool -> Bool -> Bool
True && x =  x
False && _ =  False

(||) :: Bool -> Bool -> Bool
True || _ =  True
False || x =  x

not :: Bool -> Bool
not True = False
not False = True

implies :: Bool -> Bool -> Bool
implies True False = False
implies _ _ = True

iff :: Bool -> Bool -> Bool
iff x y = x `implies` y && y `implies` x

error :: [Char] -> a
error = undefined

undefined :: a
undefined = undefined

