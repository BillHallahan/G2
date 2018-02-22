{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}
module GetNthAbstract where

import Prelude hiding (concat)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
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

{-@ concat5                  :: xss : { xss : List (List a) | sizeXs xss > 0 } 
                            -> { xs : List a | size xs = sizeXs xss &&
                                 sizeXs xss > 0 } @-}
-- concat5 ((x :+: Emp) :+: Emp) = x :+: Emp
-- concat5 (Emp :+: xss)         = concat5 xss
concat5 ((x :+: xs) :+: xss)  = x :+: concat5 (xs :+: xss)
concat5 _ = die ""