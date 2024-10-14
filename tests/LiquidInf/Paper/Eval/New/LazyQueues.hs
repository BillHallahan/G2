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
  | otherwise        = let f' = rot flen f b nil in (flen + blen, 0, Q f' nil)

rot :: Int -> [a] -> [a] -> [a] -> [a]
rot flen f b acc
  | flen == 0 = hd b `cons` acc
  | otherwise   = let r = rot (flen - 1) (tl f) (tl b) (hd b `cons` acc) in hd f `cons` r

emp :: (Int, Int, Queue a)
emp = (0, 0, Q nil nil)

-- remove :: Int -> Int -> Queue a -> (Int, Int, a, Queue a)
-- remove flen blen (Q f b)   = let (flen', blen', Q f' b') = makeq (flen - 1) blen (tl f) b
--                              in (flen' - 1, blen', hd f', Q (tl f') b')

{-@ insert :: flen:Int -> blen:Int -> a -> FBQ a flen blen -> (Int, Int, QueueN a {flen + blen + 1}) @-}
insert :: Int -> Int -> a -> Queue a -> (Int, Int, Queue a)
insert flen blen e (Q f b) = makeq flen (blen + 1) f (cons e b)

-- {-@ replicate :: n:Nat -> a -> { t:(Int, Int, QueueN a n) | x_Tuple31 t == len (frontList (x_Tuple33 t)) 
--                                                           && x_Tuple32 t == len (backList (x_Tuple33 t)) } @-}
-- replicate :: Int -> a -> (Int, Int, Queue a)
-- replicate 0 _ = emp
-- replicate n x = let (flen, blen, xs) = replicate (n-1) x in insert flen blen x xs

-- {-@ take :: n:Nat -> q:QueueGe a n -> (BalancedQ a, BalancedQ a) @-}
-- take           :: Int -> Queue a -> (Queue a, Queue a)
-- take 0 q       = (emp          , q)
-- take n q       = (insert x out , q'')
--   where
--     (x  , q')  = remove q
--     (out, q'') = take (n-1) q'

{-@ LIQUID "--no-termination" @-}