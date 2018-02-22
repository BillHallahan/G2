{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
module ConcatList where

import Prelude hiding (concat)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + 2
  @-}

{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}


{-@ concat                  :: xss : { xss : List (List a) | sizeXs xss > 0 } 
                            -> { xs : List a | size xs = sizeXs xss &&
                                 sizeXs xss > 0 } @-}
concat ((x :+: Emp) :+: Emp) = x :+: Emp
concat (Emp :+: xss)         = concat xss
concat ((x :+: xs) :+: xss)  = x :+: concat (xs :+: xss)
concat _ = die ""

{-@ concat2                 :: xss : List (List a) 
                            -> xs : List a @-}
concat2 ((x :+: xs) :+: xss)  = x :+: concat2 xss

{-@ concat3                 :: xss : List (List a) 
                            -> xs : List a @-}
concat3 ((x :+: xs) :+: xss)  = x :+: concat3 xss
concat3 _ = die "HERE"

{-@ die :: {_:String | false} -> a @-}
die :: String -> a
die _ = undefined


{-@ measure sizeXs1          :: List (List a) -> Int
    sizeXs1 (Emp)            = 0
    sizeXs1 ((:+:) xs xss)   = size xs
  @-}

{-@ concat4                  :: { xss : List (List a) | sizeXs1 xss > 0 } 
                             -> List a @-}
concat4 :: List (List a) -> List a
concat4 (Emp :+: xss)         = Emp

{-@ concat5                  :: { xss : List (List a) | 0 < sizeXs1 xss } 
                            -> List a  @-}
concat5 :: List (List a) -> List a
concat5 _ = die ""