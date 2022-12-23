{-# LANGUAGE QuasiQuotes #-}

module Main where

import Test.Tasty
import Test.Tasty.HUnit

import DeBruijn.Test
import Arithmetics.Interpreter
import Arithmetics.Test
import Lambda.Test
import NQueens.Test
import RegEx.Test
import RegEx.RegEx

import G2.Interface

import qualified Evaluations as E

tests :: TestTree
tests = testGroup "All Tests"
        [ nqueensTests
        , arithmeticsTests
        , deBruijnTests
        , regexTests ]

nqueensTests :: TestTree
nqueensTests = testGroup "N Queens"
  [ qqTestCase "4 Queens" (queensTestN 4) (allQueensSafe 4)
  , qqTestCase "5 Queens" (queensTestN 5) (allQueensSafe 5)
  , qqTestCase "6 Queens" (queensTestN 6) (allQueensSafe 6)
  , qqTestCase "7 Queens" (queensTestN 7) (allQueensSafe 7)
  , qqTestCase "8 Queens" (queensTestN 8) (allQueensSafe 8) ]

arithmeticsTests :: TestTree
arithmeticsTests = testGroup "Arithmetic"
  [ qqTestCase "Arithmetic 1" (searchBadEnv badProg)
                              (\env -> evalStmts env badProg == Nothing)
  , qqTestCase "Arithmetic 2" (envTest productSumProg) (flip evalB productSumProg)
  ]

deBruijnTests :: TestTree
deBruijnTests = testGroup "DeBruijn"
  [ qqTestCase "DeBruijn 1" (solveDeBruijn idDeBruijn) (appFunc idDeBruijn)
  , qqTestCase "DeBruijn 2" (solveDeBruijn const2Example) (appFunc const2Example)
  , qqTestCase "DeBruijn 3" (solveDeBruijn orExample) (appFunc orExample)
  ]


regexTests :: TestTree
regexTests = testGroup "Regex"
  [ qqTestCase "Regex 1" (stringSearch regex1) (match regex1)
  , qqTestCase "Regex 2" (stringSearch regex2) (match regex2)
  , qqTestCase "Regex 3" (stringSearch regex3) (match regex3)
  , qqTestCase "Regex 4" (stringSearch regex4) (match regex4)
  ]

qqTestCase :: (Eq a, Show a) => TestName -> IO (Maybe a) -> (a -> Bool) -> TestTree
qqTestCase name io_val p = do
    testCase name (do
      val <- doTimeout 180 $ io_val
      assertBool
          ("Predicate not satisfied by " ++ show val)
          (case val of
              Just (Just val') -> p val'
              _ -> False))

-- arithmeticsTests :: IO ()
-- arithmeticsTests = do
--   putStrLn "---------------------"
--   putStrLn "arithmeticsTests ----"

--   putStrLn "-- productTest"
--   timeIOActionPrint productTest
--   putStrLn ""

--   putStrLn "-- productSumTest"
--   timeIOActionPrint productSumTest
--   putStrLn ""

--   putStrLn "-- productSumAssertTest"
--   timeIOActionPrint productSumAssertTest
--   putStrLn ""

--   putStrLn "-- assertViolationTest1"
--   timeIOActionPrint assertViolationTest1
--   putStrLn ""

--   -- Technically this is non-linear integer arithm so undecidable
--   -- putStrLn "-- assertViolationTest2"
--   -- timeIOActionPrint assertViolationTest2
--   -- putStrLn ""

--   -- About 6 secs
--   putStrLn "-- assertViolationTest3"
--   timeIOActionPrint assertViolationTest3
--   putStrLn ""

--   -- About 51 secs
--   putStrLn "-- assertViolationTest4"
--   timeIOActionPrint assertViolationTest4
--   putStrLn ""




--   putStrLn "---------------------\n\n"


-- lambdaTests :: IO ()
-- lambdaTests = do
--   putStrLn "---------------------"
--   putStrLn "lambdaTests ---------"

--   putStrLn "-- lambdaTest1"
--   timeIOActionPrint lambdaTest1
--   putStrLn ""

--   putStrLn "-- lambdaTest2"
--   timeIOActionPrint lambdaTest2
--   putStrLn ""

--   putStrLn "---------------------\n\n"
--   return ()

-- debruijnTests :: IO ()
-- debruijnTests = do
--   putStrLn "---------------------"
--   putStrLn "debruijnTests -------"

--   putStrLn "-- solveDeBruijnI" -- identity
--   timeIOActionPrint $ solveDeBruijnI

--   putStrLn "-- solveDeBruijnK" -- const
--   timeIOActionPrint $ solveDeBruijnK

--   putStrLn "-- solveDeBruijnOr"
--   timeIOActionPrint $ solveDeBruijnOr

--   -- putStrLn "-- solveDeBruijnAnd"
--   -- timeIOActionPrint $ solveDeBruijnAnd

--   putStrLn "-- solveDeBruijnIte"
--   timeIOActionPrint $ solveDeBruijnIte

--   putStrLn "---------------------\n\n"
--   return ()

-- regexTests :: IO ()
-- regexTests = do
--   putStrLn "---------------------"
--   putStrLn "regexTests ----------"

--   putStrLn "-- regexTest1"
--   timeIOActionPrint regexTest1
--   putStrLn ""

--   putStrLn "-- regexTest2"
--   timeIOActionPrint regexTest2
--   putStrLn ""

--   putStrLn "---------------------\n\n"
--   return ()


main :: IO ()
main = do
    defaultMainWithIngredients
        defaultIngredients
        tests

{-
main :: IO ()
main = do
    putStrLn "main: compiles!"

    -- arithmeticsTests
    -- lambdaTests
    -- nqueensTests
    -- debruijnTests
    -- regexTests

    nqueensTests
    runArithmeticsEval
    runDeBruijnEval
    runRegExEval



    putStrLn "main: done"
-}

    -- print =<< queensTestN 6
    -- print =<< solveDeBruijnI
    -- print =<< solveDeBruijnK
    -- print =<< lambdaTest2
    
    -- putStrLn "-- Basic Test --"
    -- r <- f 8 10
    -- print r

    -- r2 <- g 7
    -- print r2

    -- r3 <- h 11
    -- print r3
    
    -- putStrLn "\n-- Bool Test --"
    -- print =<< boolTest 2
    -- print =<< boolTest 4

    -- putStrLn "\n-- maybeOrdering Test --"
    -- print =<< maybeOrderingTest (Just LT)

    -- putStrLn "\n-- Rearrange Tuples Test --"
    -- print =<< rearrangeTuples (4, 5) (-6, -4)

    -- putStrLn "\n-- Float Test --"
    -- print =<< floatTest (6.7) (9.5)

    -- putStrLn "\n-- Double Test --"
    -- print =<< doubleTest (2.2) (4.9)

    -- putStrLn "\n-- String Test --"
    -- print =<< stringTest "hiiiiiiiiiiiiiiiit!"

    -- putStrLn "\n-- Import Test --"
    -- print =<< importTest 5

    -- putStrLn "\n-- Infinite Test --"
    -- print =<< infiniteTest [5..]

    -- putStrLn "\n-- Infinite Test 2 --"
    -- print =<< infiniteTest2 [5..] 3

    -- putStrLn "\n-- Infinite Return --"
    -- ir <- infiniteReturn 8
    -- print $ fmap (headInf . tailInf) ir

-- fBad1 :: Float -> Int -> IO (Maybe Int)
-- fBad1 = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

-- fBad2 :: Int -> Int -> IO (Maybe Float)
-- fBad2 = [g2|(\y z -> \x ? x + 2 == y + z) :: Int -> Int -> Int -> Bool|]

-- f :: Int -> Int -> IO (Maybe Int)
-- f = [g2|\(y :: Int) (z :: Int) -> ?(x :: Int) | x + 2 == y + z|]

-- g :: Int  -> IO (Maybe (Int, Int))
-- g = [g2|\(a :: Int) -> ?(x :: Int) ?(y :: Int) | x < a && a < y && y - x > 10|]

-- h :: Int -> IO (Maybe [Int])
-- h = [g2|\(total :: Int) -> ?(lst :: [Int]) | sum lst == total && length lst >= 2|]

-- boolTest :: Int -> IO (Maybe Bool)
-- boolTest = [g2|\(i ::Int) -> ?(b :: Bool) | (i == 4) == b|]

-- maybeOrderingTest :: Maybe Ordering -> IO (Maybe (Maybe Ordering))
-- maybeOrderingTest = [g2|\(m1 :: Maybe Ordering) -> ?(m2 :: Maybe Ordering) | (fmap succ m1 == m2)|]

-- rearrangeTuples :: (Int, Int) -> (Int, Int) -> IO (Maybe (Int, Int))
-- rearrangeTuples = [g2|\(ux :: (Int, Int)) (yz :: (Int, Int)) -> ?(ab :: (Int, Int)) |
--                         let
--                             (u, x) = ux
--                             (y, z) = yz
--                             (a, b) = ab
--                         in
--                         (a == u || a == y)
--                             && (b == x || b == z) && (a + b == 0 )|]

-- floatTest :: Float -> Float -> IO (Maybe Float)
-- floatTest = [g2|\(f1 :: Float) (f2 :: Float) -> ?(f3 :: Float) | f1 < f3 && f3 < f2|]

-- doubleTest :: Double -> Double -> IO (Maybe Double)
-- doubleTest = [g2|\(d1 :: Double) (d2 :: Double) -> ?(d3 :: Double) | d1 <= d3 && d3 <= d2|]

-- stringTest :: String -> IO (Maybe String)
-- stringTest = [g2|\(str1 :: String) -> ?(str2 :: String) | str1 == str2 ++ "!"|]

-- importTest :: Int -> IO (Maybe Int)
-- importTest = [g2|\(x :: Int) -> ?(ans :: Int) | addTwo x == ans|]

-- infiniteTest :: [Int] -> IO (Maybe Int)
-- infiniteTest = [g2|\(xs :: [Int]) -> ?(x :: Int) | x == head xs|]

-- infiniteTest2 :: [Int] -> Int -> IO (Maybe [Int])
-- infiniteTest2 = [g2|\(xs :: [Int]) (t :: Int) -> ?(ys :: [Int]) | ys == take t xs|]

-- infiniteReturn ::  Int -> IO (Maybe (InfList Int))
-- infiniteReturn = [g2|\(t :: Int) -> ?(ys :: InfList Int) | headInf ys == t |]
