module Concat where

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}


{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss
  @-}

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ concat                  :: xss: { xss : List (List a) | sizeXs xss > 0 }
                            -> { xs : List a | size xs = sizeXs xss } @-}
concat    :: List (List a) -> List a
concat ((x :+: Emp) :+: Emp) = x :+: Emp
concat (Emp :+: xss)         = concat xss
concat ((x :+: xs) :+: xss)  = x :+: concat (xs :+: xss)
