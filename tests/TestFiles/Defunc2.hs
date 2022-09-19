module Defunc2 where

data IList = I Int IList 
           | INil
           deriving Eq

data FList = F (Int -> Int) FList
           | FNil

add1 :: Int -> Int
add1 x = x + 1

sub1 :: Int -> Int
sub1 x = x - 1

square :: Int -> Int
square x = x * x

funcMap :: FList -> IList -> IList
funcMap (F f fs) (I i is) = I (f i) (funcMap fs is)
funcMap FNil i = i
funcMap _ _ = INil
