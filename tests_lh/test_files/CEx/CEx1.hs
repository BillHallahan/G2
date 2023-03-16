{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module CEx1 where

import Prelude hiding (zipWith)

infixr 9 :+:

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
        size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ zipWith :: (Int -> Int -> Int) -> xs:List Int -> ys:List Int -> {zs : List Int | size ys == size zs } @-}
zipWith   :: (Int -> Int -> Int) -> List Int -> List Int -> List Int
zipWith _ Emp Emp               = Emp
zipWith f (x :+: xs) (y :+: ys) = f x y :+: zipWith f xs ys
zipWith f _          _          = die  "Bad call to zipWith"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)



