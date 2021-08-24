module UnsafePerformIO1 where

import System.IO.Unsafe

f :: Int -> Int
f x = unsafePerformIO $ do
    y <- return (x + 1)
    return (y + 1)