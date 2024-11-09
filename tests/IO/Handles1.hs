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