{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
 
module Error3 where

z   :: (a -> a) -> a -> a


{-@ z :: (a -> a) -> a -> a @-}
z f x  = f x
