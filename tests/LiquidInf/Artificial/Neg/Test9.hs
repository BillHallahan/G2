{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module ListQualif ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import qualified Data.Map as M

infixr 9 :+:

data List a = Emp | (:+:) a (List a)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs @-}

{-@ invariant {v:List a | 0 <= size v} @-}

{-@ map :: (Int -> List Int) -> xs:List Int -> { ys:List (List Int) | size xs == size ys } @-}
map :: (Int -> List Int) -> List Int -> List (List Int)
map f Emp        = Emp
map f (x :+: xs) = f x :+: map f xs

{-@ measure sizeXs          :: List (List a) -> Int
    sizeXs (Emp)            = 0
    sizeXs ((:+:) xs xss)   = size xs + sizeXs xss @-}

{-@ concat :: xs:List (List Int) -> { ys:List Int | size ys <= sizeXs xs } @-}
concat :: List (List Int) -> List Int
concat Emp = Emp
concat (xs :+: _) = xs

{-@ expand :: (Int -> List Int) -> xs:List Int -> { ys:List Int | size ys <= size xs } @-}
expand :: (Int -> List Int) -> List Int -> List Int
expand f xs = concat (map f xs)

