{-# LANGUAGE MagicHash #-}
module UnsafeIO where

import Data.IORef
import System.IO.Unsafe (unsafeDupablePerformIO)
import GHC.Exts (runRW#)

num :: IORef Int
num = unsafeDupablePerformIO (newIORef 123)

readNum :: Int
readNum = unsafeDupablePerformIO (readIORef num)

numTest :: Int -> Int
numTest x = if x > readNum then 0 else 1

rwNum :: Int
rwNum = runRW# (\_s -> 123)

rwNumTest :: Int -> Int
rwNumTest x = if x > rwNum then 0 else 1
