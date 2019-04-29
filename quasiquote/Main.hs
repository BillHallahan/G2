{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.QuasiQuotes.QuasiQuotes



main :: IO ()
main = do
    r <- f 8 10
    print r

    r2 <- g 7
    print r2

    r3 <- h 11
    print r3

    print =<< boolTest 2
    print =<< boolTest 4

    print =<< maybeOrderingTest (Just LT)

    print =<< rearrangeTuples (4, 5) (-6, -4)

    print =<< floatTest (6.7) (9.5)

    print =<< doubleTest (2.2) (4.9)

    print =<< stringTest "hiiiiiiiiiiiiiiiit!"

    print =<< funcTest ((+ 1) :: Int -> Int) ((+ 2) :: Int -> Int)


-- fBad1 :: Float -> Int -> IO (Maybe Int)
-- fBad1 = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

-- fBad2 :: Int -> Int -> IO (Maybe Float)
-- fBad2 = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

f :: Int -> Int -> IO (Maybe Int)
-- f = [g2|(\y z -> x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]
f = [g2|!(y :: Int) !(z :: Int) -> ?(x :: Int) | x + 2 == y + z|]

g :: Int  -> IO (Maybe (Int, Int))
-- g = [g2|(\a -> x y ? x < a && a < y && y - x > 10) :: Int -> Int -> Int -> Bool|]
g = [g2|!(a :: Int) -> ?(x :: Int) ?(y :: Int) | x < a && a < y && y - x > 10|]

h :: Int -> IO (Maybe [Int])
-- h = [g2|(\total -> lst ? sum lst == total && length lst >= 2) :: Int -> [Int] -> Bool|]
h = [g2|!(total :: Int) -> ?(lst :: [Int]) | sum lst == total && length lst >= 2|]

boolTest :: Int -> IO (Maybe Bool)
-- boolTest = [g2|(\i -> b ? (i == 4) == b) :: Int -> Bool -> Bool|]
boolTest = [g2|!(i ::Int) -> ?(b :: Bool) | (i == 4) == b|]

maybeOrderingTest :: Maybe Ordering -> IO (Maybe (Maybe Ordering))
-- maybeOrderingTest = [g2|(\m1 -> m2 ? fmap succ m1 == m2) :: Maybe Ordering -> Maybe Ordering -> Bool|]
maybeOrderingTest = [g2|!(m1 :: Maybe Ordering) -> ?(m2 :: Maybe Ordering) | (fmap succ m1 == m2)|]

rearrangeTuples :: (Int, Int) -> (Int, Int) -> IO (Maybe (Int, Int))
-- rearrangeTuples = [g2| ( \ux yz -> ab ?
rearrangeTuples = [g2|!(ux :: (Int, Int)) !(yz :: (Int, Int)) -> ?(ab :: (Int, Int)) |
                        let
                            (u, x) = ux
                            (y, z) = yz
                            (a, b) = ab
                        in
                        (a == u || a == y)
                            && (b == x || b == z) && (a + b == 0 )|]

floatTest :: Float -> Float -> IO (Maybe Float)
-- floatTest = [g2| (\f1 f2 -> f3 ? f1 < f3 && f3 < f2) :: Float -> Float -> Float -> Bool |]
floatTest = [g2|!(f1 :: Float) !(f2 :: Float) -> ?(f3 :: Float) | f1 < f3 && f3 < f2|]

doubleTest :: Double -> Double -> IO (Maybe Double)
-- doubleTest = [g2| (\d1 d2 -> d3 ? d1 <= d3 && d3 <= d2) :: Double -> Double -> Double -> Bool |]
doubleTest = [g2|!(d1 :: Double) !(d2 :: Double) -> ?(d3 :: Double) | d1 <= d3 && d3 <= d2|]

stringTest :: String -> IO (Maybe String)
-- stringTest = [g2| (\str1 -> str2 ? str1 == str2 ++ "!") :: String -> String -> Bool |]
stringTest = [g2|!(str1 :: String) -> ?(str2 :: String) | str1 == str2 ++ "!"|]

funcTest :: (Int -> Int) -> (Int -> Int) -> IO (Maybe Int)
funcTest = [g2|!(f :: (Int -> Int)) !(g :: Int -> Int) -> ?(ans :: Int) | (f (g 10)) == ans|]


