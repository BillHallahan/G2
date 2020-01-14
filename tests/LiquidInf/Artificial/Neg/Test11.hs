{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Test11 where

import qualified Data.Map as M

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data D a = Emp | R a deriving (Eq, Ord, Show)

{-@ measure size :: D a -> Int
    size (Emp) = 0
    size (R x) = 1
  @-}

{-@ invariant {v:D a | 0 <= size v} @-}

{-@ type DN a N  = {v:D a | size v = N} @-}

{-@ mapR :: (a -> b) -> xa : D a -> D b @-}
mapR :: (a -> b) -> D a -> D b
mapR f Emp = Emp
mapR f (R x) = R (f x)

type Point   = D Int
{-@ type PointN N = DN Int N @-}

{-@ f :: k:Nat -> D (PointN k) -> M.Map {v:Int | v < k} Int @-}
f   :: Int -> D Point -> M.Map Int Int
f k ps = g (\_ -> (-1, 1)) ps

{-@ g :: (Ord k) => (D Int -> (k, v)) -> D (D Int) -> M.Map k v @-}
g :: (Ord k) => (D Int -> (k, v)) -> D (D Int) -> M.Map k v
g fm xs = kvm
  where
    kvs   = mapR fm xs
    kvsm  = app insertR M.empty kvs
    kvm   = M.map outR kvsm

{-@ insertR :: Ord k => (k, v) -> M.Map k (D v) -> M.Map k (D v) @-}
insertR (k,v) m = M.insert k (R v) m

app :: (a -> b -> b) -> b -> D a -> b
app _  b Emp = b
app op b (R x) = x `op` b

{-@ outR :: { xs : D a | size xs > 0 } -> a @-}
outR (R x) = x
outR Emp = die "Cannot call outR with empty D"