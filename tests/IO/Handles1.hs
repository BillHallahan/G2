{-# LANGUAGE LambdaCase #-}

module Handles1 where

import System.IO

compareInitChars :: IO (Char, Char, Bool)
compareInitChars = do
    c1 <- hGetChar stdin
    c2 <- hGetChar stdin
    return (c1, c2, c1 == c2)

take10Contents :: IO String
take10Contents = do
    l <- hGetContents stdin
    return (take 10 l)

output1 :: IO ()
output1 = mapM_ (hPutChar stdout) ['A', 'B', 'C']

output2 :: IO ()
output2 = do
    hPutStr stdout "ABC"
    hPutStrLn stdout "DEF"
    hPutStr stdout "GHI"

output3 :: IO ()
output3 = do
    putStrLn "---"
    putStr "x = "
    print 6

interact1 :: IO ()
interact1 = interact (\case "ABC" -> "EFG"; s -> s)