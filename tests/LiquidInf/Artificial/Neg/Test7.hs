{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (f) where

infixr 9 :+:

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

data Map k a = Assocs [(k, a)]

insert :: Ord k => k -> a -> Map k a -> Map k a
insert k a (Assocs kas) = Assocs (insertBy keycmp (k, a) kas)
  where
    keycmp (k1, _) (k2, _) = k1 `compare` k2

insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _   x [] = [x]
insertBy cmp x ys@(y:ys')
 = case cmp x y of
     GT -> y : insertBy cmp x ys'
     _  -> x : ys

{-@ f :: Ord k => k -> b -> Map k (List b) -> Map k ({xs:List b | 0 < size xs}) @-}
f k v m = insert k (v :+: Emp) m
