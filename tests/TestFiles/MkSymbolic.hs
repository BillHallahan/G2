-- Testing the mkSymbolic function, which generates a fresh symbolic variable

module MkSymbolic where

import G2.Symbolic

f :: IO (Ordering, Ordering)
f = do
    x <- mkSymbolic 
    y <- mkSymbolic
    return (compare x 0, compare y 0)