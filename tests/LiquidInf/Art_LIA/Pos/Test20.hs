{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--maxparams=3"    @-}

module LazyQueue (Q, size, qsize, size) where

{-@ die :: {v:String | false} -> a @-}
die x = error x

{-@ invariant {v:[a] | size v >= 0} @-}
{-@ invariant {v:[a] | size v == len v} @-}

{-@ measure size @-}
size      :: [a] -> Int
size []     = 0
size (_:xs) = 1 + size xs

{-@ data Q a = Q {
      front :: [a]
    , back  :: {v:[a] | size v == 0}
    }
@-}
data Q a = Q
  { front :: [a]
  , back  :: [a]
  }

{-@ measure qsize @-}
qsize :: Q a -> Int
qsize (Q { front = f, back = b}) = size f + size b

data X = X

{-@ t :: Int -> { q:Q X | qsize q > 0 } -> { q2:[X] | size q2 <= qsize q } @-}
t :: Int -> Q X -> [X]
t n  (Q f b) = c (tl f)

c :: [a] -> [a]
c f = []

{-@ tl :: { xs: [a] | size xs > 0 } -> {v:[a] | size v = size xs - 1}  @-}
tl ( (_:xs)) = xs
tl _ = die "empty"
