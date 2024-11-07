module IORef1 where

import Data.IORef
import System.IO.Unsafe

unsafeF :: Int -> Int
unsafeF = unsafePerformIO . f

f :: Int -> IO Int
f x = do
    r <- newIORef x
    modifyIORef r (+ 1)
    readIORef r

{-# NOINLINE glob #-}
glob :: IORef Int
glob = unsafePerformIO $ newIORef 0

unsafeG :: Int -> (Int, Int, Int)
unsafeG = unsafePerformIO . g

g :: Int -> IO (Int, Int, Int)
g x = do
    writeIORef glob 0
    let y = if x > 0 then x + 1 else x - 1
    v1 <- readIORef glob
    modifyIORef glob (+ y)
    v2 <- readIORef glob
    modifyIORef glob (+ y)
    v3 <- readIORef glob
    return (v1, v2, v3)