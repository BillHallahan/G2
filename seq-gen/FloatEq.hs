module FloatEq where

import Data.Functor.Classes

floatEq :: Float -> Float -> Bool
floatEq x y | isNaN x = isNaN y
floatEq x y = x == y

eqFloatList :: [Float] -> [Float] -> Bool
eqFloatList = liftEq floatEq