module LazyQueues (insert) where

import Prelude hiding (replicate, take)

nil :: [a]
nil = []

cons :: a -> [a] -> [a]
cons x xs = x:xs

tl :: [a] -> [a]
tl (_:xs) =  xs
tl _           = die "empty SList"

hd :: [a] -> a
hd (x:_)  = x
hd _             = die "empty SList"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data Queue a = Q
  { front :: [a]
  , back  :: [a]
  }

{-@ measure frontSize :: Queue a -> Int
frontSize (Q f _) = len f
@-}

{-@ measure backSize :: Queue a -> Int
backSize (Q _ b) = len b
@-}

{-@ type BalancedQ a = { q:Queue a | frontSize q >= backSize q } @-}

{-@ type QueueN a N = {v:BalancedQ a | frontSize q + backSize q == N } @-}
{-@ type QueueGe a N = {v:BalancedQ a | frontSize q + backSize q >= N } @-}

{-@ type FBQ a F B = { q:BalancedQ a | frontSize q == F && backSize q == B } @-}

makeq :: Int -> Int -> [a] -> [a] -> (Int, Int, Queue a)
makeq flen blen f b
  | blen <= flen = (flen, blen, Q f b)
  | otherwise        = let f' = rot f b nil in (flen + blen, 0, Q f' nil)

rot :: [a] -> [a] -> [a] -> [a]
rot f b acc
  | [] <- f = hd b `cons` acc
  | otherwise   = let r = rot (tl f) (tl b) (hd b `cons` acc) in hd f `cons` r

emp :: (Int, Int, Queue a)
emp = (0, 0, Q nil nil)

{-@ insert :: flen:Int -> blen:Int -> a -> FBQ a flen blen -> (Int, Int, BalancedQ a) @-}
insert :: Int -> Int -> a -> Queue a -> (Int, Int, Queue a)
insert flen blen e (Q f b) = makeq flen (blen + 1) f (cons e b)

{-@ LIQUID "--no-termination" @-}