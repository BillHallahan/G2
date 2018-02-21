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

{-@ concat2                 :: xss : List (List a) 
                            -> xs : List a @-}
concat2 ((x :+: xs) :+: xss)  = x :+: concat2 xss