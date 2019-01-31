{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module TypeClass5 where

class TC a where
    f :: a -> a
    g :: a -> a
    h :: a -> a

instance TC [(a, String)] where
    f = id
    g = id
    h = id

run :: TC [(a, String)] => a -> [(a, String)]
run x = f [(x, "Test")]

run2 :: TC [(a, String)] => [(a, String)] -> [(a, String)]
run2 = f