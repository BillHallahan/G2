{-# LANGUAGE QuasiQuotes #-}

module Main where

import G2.QuasiQuotes.QuasiQuotes
import TestFunctions

import Data.Time.Clock
import Data.Maybe

main :: IO ()
main = do
    -- debugging
    mergeEffectiveTests

debugging :: IO ()
debugging = do
    -- timeIOActionPrint "compress4 Bad" $ [g2| \(a :: Int) -> ?(xs :: [Int]) | compressTest4_2 a xs |] 2
    -- timeIOActionPrint "compress4SM Bad" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) | compressTest4_2 a xs |] 2
    return ()


mergeEffectiveTests :: IO ()
mergeEffectiveTests = do
    -- timeIOActionPrint "compress5" $ [g2| \(a :: Int) -> ?(xs :: [Int]) | compressTest5 a xs |] 2
    -- timeIOActionPrint "compress5SM" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) | compressTest5 a xs |] 2

    -- timeIOActionPrint "compress4" $ [g2| \(a :: Int) -> ?(xs :: [Int]) | compressTest4 a xs |] 2
    -- timeIOActionPrint "compress4SM" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) | compressTest4 a xs |] 2

    -- timeIOActionPrint "compress" $
    --     [g2| \(ys :: [Int]) -> ?(xs :: [Int]) | compress xs == ys |] [1, 2, 3, 4, 5]
    -- compressTestCallM [0..6]
    -- mapM_ (\x -> do
    --             print x
    --             compressTestCallM [0..x]) [5, 6]

    -- timeIOActionPrint "subseqOfTestM" $
    --     [g2M| \(a :: [Int]) -> ?(b :: [Int])
    --         | isSubsequenceOf' a b |] [1,2]
     -- compressTestCallM [0..2]

    -- timeIOActionPrint "compressM" $
    --     [g2M| \(ys :: [Int]) -> ?(xs :: [Int]) | compressTest xs ys |] [0..2]

    -- compressTestCallM [0..4]
    timeIOActionPrint "compressM" $
        [g2M| \(ys :: [Int]) -> ?(xs :: [Int]) | compress xs == ys |] [70..72]
    -- mapM_ (\x -> do
    --             print x
    --             compressTestCall [0..x]
    --             compressTestCallM [0..x]) [1 .. 5]

    -- mapM_ (\x -> do
    --             print x
    --             subseqOfTestCall x
    --             subseqOfTestCallM x) [1 .. 10]

    -- mapM_ (\x -> do
    --             print x
    --             sumsEvenTestCall x
    --             sumsEvenTestCallM x) [1 .. 10]

    -- timeIOActionPrint "subseqOfTest" $ [g2| \(a :: [Int]) -> ?(b :: [Int]) | subseqOfTest2 a b |] [1,2]
    -- timeIOActionPrint "subseqOfTestSM" $ [g2M| \(a :: [Int]) -> ?(b :: [Int]) | subseqOfTest2 a b |] [1,2]

    -- timeIOActionPrint "lengthTest" $ [g2| \(a :: [Int]) -> ?(b :: [Int]) | lengthTest2 a b |] [1,2]
    -- timeIOActionPrint "lengthTestSM" $ [g2M| \(a :: [Int]) -> ?(b :: [Int]) | lengthTest2 a b |] [1,2]

    -- timeIOActionPrint "sumEvensTest" $ [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 5
    -- timeIOActionPrint "sumEvensTestSM" $ [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 5

    -- timeIOActionPrint "sumEvensTest" $ [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 1
    -- timeIOActionPrint "sumEvensTestSM" $ [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] 1


    -- timeIOActionPrint "foldrTest" $ [g2| \(z :: Int) -> ?(xs :: [Maybe Int]) | foldrTest z xs |] 0
    -- timeIOActionPrint "foldrTestSM" $ [g2M| \(z :: Int) -> ?(xs :: [Maybe Int]) | foldrTest z xs |] 0

    -- timeIOActionPrint "foldrTest2" $ [g2| \(z :: Int) -> ?(xs :: [Maybe Int]) ?(ys :: [Maybe Int]) | foldrTest2 z xs ys |] 0
    -- timeIOActionPrint "foldrTest2SM" $ [g2M| \(z :: Int) -> ?(xs :: [Maybe Int]) ?(ys :: [Maybe Int]) | foldrTest2 z xs ys |] 0

    -- timeIOActionPrint "divideTest" $ [g2| \(a :: Int) -> ?(b :: Int) ?(c :: Int) ?(d :: Int) | divideTest c d a b |] 5
    -- timeIOActionPrint "divideTestSM" $ [g2M| \(a :: Int) -> ?(b :: Int) ?(c :: Int) ?(d :: Int) | divideTest c d a b |] 5

    -- timeIOActionPrint "LuhnFormula" $ [g2| \(a :: Int) -> ?(idn :: [Int]) | validateLuhn a idn |] 15
    -- timeIOActionPrint "LuhnFormulaSM" $ [g2M| \(a :: Int) -> ?(idn :: [Int]) | validateLuhn a idn |] 15

    -- timeIOActionPrint "replGetTest" $ [g2| \(i :: Int) -> ?(j :: Int) ?(k :: Int) | replGetTest i j k |] 3
    -- timeIOActionPrint "replGetTestSM" $ [g2M| \(i :: Int) -> ?(j :: Int) ?(k :: Int) | replGetTest i j k |] 3
    return ()

-- compressTestCall :: [Int] -> IO ()
-- compressTestCall xs =
--     timeIOActionPrint "compress" $
--         [g2| \(ys :: [Int]) -> ?(xs :: [Int]) | compressTest xs ys |] xs

-- compressTestCallM :: [Int] -> IO ()
-- compressTestCallM xs =
--     timeIOActionPrint "compressM" $
--         [g2M| \(ys :: [Int]) -> ?(xs :: [Int]) | compressTest xs ys |] xs

-- subseqOfTestCall :: Int -> IO ()
-- subseqOfTestCall x =
--     timeIOActionPrint "subseqOfTest" $
--         [g2| \(x :: Int) (a :: [Int]) -> ?(b :: [Int])
--            | subseqOfTestP x a b |] x [1,2,1,3]

-- subseqOfTestCallM :: Int -> IO ()
-- subseqOfTestCallM x =
--     timeIOActionPrint "subseqOfTestM" $
--         [g2M| \(x :: Int) (a :: [Int]) -> ?(b :: [Int])
--             | subseqOfTestP x a b |] x [1,2,1,3]

-- sumsEvenTestCall :: Int -> IO ()
-- sumsEvenTestCall x =
--     timeIOActionPrint "sumEvensTest" $
--         [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] x

-- sumsEvenTestCallM :: Int -> IO ()
-- sumsEvenTestCallM x =
--     timeIOActionPrint "sumEvensTestM" $
--         [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensTest xs x |] x

-- sampleTests :: IO ()
-- sampleTests = do
    -- timeIOActionPrint "peanoAdd" $ [g2| \(p1 :: Peano) -> ?(p2 :: Peano) | fstIsEvenAddToFour p1 p2 |] Zero
    -- timeIOActionPrint "peanoAddSM" $ [g2M| \(p1 :: Peano) -> ?(p2 :: Peano) | fstIsEvenAddToFour p1 p2 |] Zero

-- samePerfTests :: IO ()
-- samePerfTests = do
    -- timeIOActionPrint "mccarthy" $ [g2| \(y :: Int) -> ?(x :: Int) | greaterThan10Less x y |] 145
    -- timeIOActionPrint "mccarthySM" $ [g2M| \(y :: Int) -> ?(x :: Int) | greaterThan10Less x y |] 145

    -- timeIOActionPrint "vectorAdd" $ [g2| \(a :: [Int]) (res :: [Int]) -> ?(b :: [Int]) | vectorAddTest a b res |] [1,2,3,2,7,4,5,6,4,5,6,7,8,9] [3,9,9,9,9,9,9,9,2,3,4,5,6,3]
    -- timeIOActionPrint "vectorAddSM" $ [g2M| \(a :: [Int]) (res :: [Int]) -> ?(b :: [Int]) | vectorAddTest a b res |] [1,2,3,2,7,4,5,6,4,5,6,7,8,9] [3,9,9,9,9,9,9,9,2,3,4,5,6,3]

    -- timeIOActionPrint "g2" $ [g2| \(a :: Int) -> ?(b :: [Int]) | sieveTest a b |] 5
    -- timeIOActionPrint "g2M" $ [g2M| \(a :: Int) -> ?(b :: [Int]) | sieveTest a b|] 5

-- mergeSlowdownTests :: IO ()
-- mergeSlowdownTests = do
    -- timeIOActionPrint "sumEvensTestSlow" $ [g2| \(x :: Int) -> ?(xs :: [Int]) | sumEvensSlow xs x |] 3
    -- timeIOActionPrint "sumEvensTestSlowSM" $ [g2M| \(x :: Int) -> ?(xs :: [Int]) | sumEvensSlow xs x |] 3

    -- timeIOActionPrint "compress" $ [g2| \(ys :: [Int]) -> ?(xs :: [Int]) | compressTest xs ys |] [1,2,3]
    -- timeIOActionPrint "compressSM" $ [g2M| \(ys :: [Int]) -> ?(xs :: [Int]) | compressTest xs ys |] [1,2,3]

    -- timeIOActionPrint "compress2" $ [g2| \(a :: Int) -> ?(xs :: [Int]) ?(ys :: [Int]) | compressTest2 a xs ys |] 1
    -- timeIOActionPrint "compress2SM" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) ?(ys :: [Int]) | compressTest2 a xs ys |] 1

    -- timeIOActionPrint "compress3" $ [g2| \(a :: Int) -> ?(xs :: [Int]) | compressTest3 a xs |] 11
    -- timeIOActionPrint "compress3SM" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) | compressTest3 a xs |] 11

    -- timeIOActionPrint "runLengthEncode" $ [g2| \(a :: Int) -> ?(xs :: [Int]) | runLengthEncodeTest a xs |] 4
    -- timeIOActionPrint "runLengthEncodeSM" $ [g2M| \(a :: Int) -> ?(xs :: [Int]) | runLengthEncodeTest a xs |] 4

    -- timeIOActionPrint "reverseTest" $ [g2| \(len :: Int) -> ?(a :: [Int]) | reverseTest len a |] 15
    -- timeIOActionPrint "reverseTestSM" $ [g2M| \(len :: Int) -> ?(a :: [Int]) | reverseTest len a |] 15

    -- timeIOActionPrint "range" $ [g2| \(lo:: Int) -> ?(hi :: Int) | rangeAssert lo hi |] 2
    -- timeIOActionPrint "rangeSM" $ [g2M| \(lo :: Int) -> ?(hi :: Int) | rangeAssert lo hi |] 2


timeIOAction :: IO a -> IO (a, NominalDiffTime)
timeIOAction action = do
  start <- getCurrentTime
  res <- action
  end <- getCurrentTime
  let diff = diffUTCTime end start
  return (res, diff)

timeIOActionPrint :: Show a => String -> IO a -> IO ()
timeIOActionPrint nm action = do
  (res, time) <- timeIOAction action
  putStrLn nm
  putStrLn $ show res
  putStrLn $ "time: " ++ show time
