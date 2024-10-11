module LazyQueues (remove) where

import Prelude hiding (replicate, take)

nil :: (Int, [a])
nil = (0, [])

cons :: Int -> a -> [a] -> (Int, [a])
cons n x xs = (n+1, x:xs)

tl :: Int -> [a] -> (Int, [a])
tl n (_:xs) = (n-1, xs)
tl _ _           = die "empty SList"

hd :: [a] -> a
hd (x:_)  = x
hd _             = die "empty SList"

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data Queue a = Q
  { front :: [a]
  , back  :: [a]
  }

{-@ measure frontList @-}
frontList :: Queue a -> [a]
frontList (Q f _) = f

{-@ measure backList @-}
backList :: Queue a -> [a]
backList (Q _ b) = b

{-@ measure queueLen @-}
queueLen :: Queue a -> Int
queueLen (Q f b) = size f + size b

{-@ type BalancedQ a = { q:Queue a | len (frontList q) >= len (backList q) } @-}

{-@ type QueueN a N = {v:BalancedQ a | queueLen q == N } @-}
{-@ type QueueGe a N = {v:BalancedQ a | queueLen q >= N } @-}

makeq :: Int -> Int -> [a] -> [a] -> (Int, Int, Queue a)
makeq flen blen f b
  | blen <= flen = (flen, blen, Q f b)
  | otherwise        = let (l, f') = rot flen blen 0 f b nil in (l, 0, Q f' nil)

rot :: Int -> Int -> Int -> [a] -> [a] -> [a] -> (Int, [a])
rot flen blen alen f b acc
  | flen == 0 = (alen, hd b `cons` acc)
  | otherwise   = let (l, r) = rot (flen - 1) (blen - 1) (alen + 1) (tl f) (tl b) (hd b `cons` acc) in (l + 1, hd f `cons` r)

emp :: (Int, Int, Queue a)
emp = (0, 0, Q (snd nil) (snd nil))

remove :: Int -> Int -> Queue a -> (Int, Int, a, Queue a)
remove flen blen (Q f b)   = let (flen', f') = tl flen f
                                 (flen'', blen', Q f'' b') = makeq flen' blen f' b
                             in (flen'' - 1, blen', hd f'', Q f'' b')

insert :: Int -> Int -> a -> Queue a -> (Int, Int, Queue a)
insert flen blen e (Q f b) = let (blen', b') = (cons blen e b) in makeq flen blen' f b'

{-@ replicate :: n:Nat -> a -> { t:(Int, Int, QueueN a n) | x_31 t + x_32 t == queueSize (x_33 t) } @-}
replicate :: Int -> a -> (Int, Int, Queue a)
replicate 0 _ = emp
replicate n x = let (flen, blen, xs) = replicate (n-1) x in insert flen blen x xs

-- {-@ take :: n:Nat -> q:QueueGe a n -> (BalancedQ a, BalancedQ a) @-}
-- take           :: Int -> Queue a -> (Queue a, Queue a)
-- take 0 q       = (emp          , q)
-- take n q       = (insert x out , q'')
--   where
--     (x  , q')  = remove q
--     (out, q'') = take (n-1) q'

{-@ LIQUID "--no-termination" @-}