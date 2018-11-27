module LHPOPL where

-- 3) LH

{-@ type Salary = { s:Double | s > 0 } @-}
type Salary = Double

-- {-@ giveRaises :: { r:Double | r > 0 } -> [Salary] -> [Salary] @-}
-- giveRaises :: Double -> [Salary] -> [Salary]
-- a _ [] = []
-- giveRaises r (s:xs) = addPercentage r s:giveRaises r xs

-- {-@ addPercentage :: {d1:Double | d1 > 0 } -> {d2:Double | d2 > 0 } -> {d3:Double | d3 > 0 } @-}
-- addPercentage :: Double -> Double -> Double
-- addPercentage r s = r * s + s

{-@ maxRaise :: { r:Double | r > 0 } -> {v:[Salary] | len v > 0 } -> { s:Double | s >= 0 } @-}
maxRaise :: Double -> [Salary] -> Double
maxRaise _ [] = error "Empty list"
maxRaise r (s:[]) = calcRaise r s
maxRaise r (s:xs) =
    let
        m = calcRaise r s
        m' = maxRaise r xs
    in
    if m > m' then m else m'

-- {-@ calcRaise :: { d:Double | d > 0 } -> Salary -> { dr:Double | dr > 0 } @-}
{-@ calcRaise :: Double -> Salary -> Double @-}
calcRaise :: Double -> Salary -> Double
calcRaise r s = r * s

{-@ salaries1 :: [Salary] @-}
salaries1 :: [Salary]
salaries1 = [100000, 200000]

salaries2 :: [Salary]
salaries2 = [50000, 60000]

{-@ allSalaries :: [Salary] @-}
allSalaries :: [Salary]
allSalaries = salaries1 ++ salaries2
