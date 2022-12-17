{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-} 

module PropSize where

import Prelude hiding (length)

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ badLength :: l:List a -> {v:Int | l = l} @-} 
badLength            :: List a -> Int
badLength _        = 0

{-@ prop_size :: TRUE @-}
prop_size  = lAssert (badLength (1 :+: Emp) == 1)

{-@ type TRUE = {v:Bool | v} @-}

{-@ lAssert :: TRUE -> TRUE @-}
lAssert True  = True
lAssert False = die "Assert Fails!"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)
