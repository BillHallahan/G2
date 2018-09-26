module NumOrd where

{-@ sub :: Num a => {x:a | x > 0} -> {y:a | y >= 0} @-}
sub :: Num a => a -> a 
sub x = x - 1


{-@ f :: {x:a | x > 0} -> {y:a | y > 0} @-}
f :: a -> a 
f x = x