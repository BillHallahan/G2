-- Testing the mkSymbolic function, which generates a fresh symbolic variable

module MkSymbolic where

import G2.Symbolic

f :: IO (Ordering, Ordering)
f = do
    x <- mkSymbolic 
    y <- mkSymbolic
    return (compare x 0, compare y 0)

testAssume :: IO Int
testAssume = do
    x <- mkSymbolic
    y <- mkSymbolic
    assumeIO (x > y)
    case x - y > 0 of
        True -> return 1
        False -> error "impossible"

testAssert :: IO Int
testAssert = do
    x <- mkSymbolic
    assertIO (x < x + 1)
    return 0