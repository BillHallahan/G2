\begin{code}
{-# LANGUAGE BangPatterns #-}

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module MapReduce (mapReduce) where

import qualified Data.Map as M
-- import List3
import Prelude hiding (map, reduce, concat)
expand   :: (Int -> List Int) -> List Int -> List Int

mapReduce :: (Int -> List Int) -> List Int -> List Int
mapReduce fm xs = expand fm xs     -- step 1

{-@ expand  :: (Int -> List Int) -> List Int -> List Int @-}
expand f xs = concat (map f xs)

infixr 9 :+:

map       :: (Int -> List Int) -> List Int -> List (List Int)
concat    :: List (List Int) -> List Int

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
        size (Emp)        = 0
    size ((:+:) x xs) = 1
  @-}

{-@ map :: (Int -> List Int) -> x:List Int -> List (List Int) @-}
map f Emp        = Emp
map f (x :+: xs) = f x :+: Emp

{-@ measure si      :: List (List a) -> Int
    si (Emp) = 0
    si ((:+:) x xs) = size x
  @-}

{-@ concat ::  x:List (List Int) -> {y:List Int| size y = si x} @-}
concat _ = Emp

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

\end{code}

\begin{code}

expand2   :: (Int -> List Int) -> List Int
{-@ expand2  :: (Int -> List Int) -> List Int @-}
expand2 f = concat2 (f 1 :+: Emp)

concat2    :: List (List Int) -> List Int
{-@ concat2 ::  x:List (List Int) -> {y:List Int| 0 = si x} @-}
concat2 _ = Emp

\end{code}