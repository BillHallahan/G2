module IdentityTest where

import Data.Functor.Identity

call :: Int -> (Int, Int)
call x = runIdentity (twoAdditions x)

twoAdditions :: Int -> Identity (Int, Int)
twoAdditions x = do
    y <- addition x 8
    z <- addition x 10
    return (y, z) 

addition :: Int -> Int -> Identity Int
addition x y = return $ x + y