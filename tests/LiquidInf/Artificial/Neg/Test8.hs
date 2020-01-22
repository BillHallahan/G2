{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined () where

data R = Emp
            | D
              deriving (Eq, Ord, Show)

{-@ measure size      :: R -> Int
    size (Emp) = 0
    size D = 1
  @-}

{-@ invariant {v:R | 0 <= size v} @-}

insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _   x [] = []
insertBy cmp x ys@(y:ys')
 = case cmp x y of
     GT -> [x]
     _  -> []

{-@ f :: Ord k => k -> b -> [k] -> [{ xs:k | false }] @-}
f :: Ord k => k -> b -> [k] -> [k]
f k v m = insertBy compare k m