module Combined ( List
                , test_nearest) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)

import qualified Data.List as L

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

{-@ type ListN a N  = {v:List a | size v = N} @-}

empty     :: List a
empty = Emp

add       :: a -> List a -> List a
add x xs = x :+: xs

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

zipWith   :: List a -> List a -> List a
zipWith Emp Emp               = Emp
zipWith (x :+: xs) (y :+: ys) = x :+: zipWith xs ys
zipWith  _          _          = die  "Bad call to zipWith"

distance :: List Double -> List Double -> Double
distance px py = foldr (+) 0 $ zipWith px py

{-@ nearest :: Map Int {_ : (List Double) | false} -> (List Double) -> (Int, List Double) @-}
nearest   :: Map Int (List Double) -> List Double -> (Int, List Double)
nearest centers p = minimumBy f keyList
  where
    keyList = toList centers
    f x1 x2 = compare (distance (snd x1) p) (distance (snd x2) p)

test_nearest = nearest (fromList [(0, p0), (1, p1)]) p
  where
    p, p0, p1 :: List Double
    p0 = add 0.0 empty
    p1 = add 0.0 empty
    p  = add 1.1 empty


data Map k a = Assocs [(k, a)]

fromList :: Ord k => [(k,a)] -> Map k a
fromList kas = Assocs (sby keycmp $ reverse kas) 
  where
    keycmp (k1, _) (k2, _) = k1 `compare` k2

    iby _ x [] = [x]
    iby cmp x ys@(y:ys') = case cmp x y of
        GT -> y : iby cmp x ys'
        _ -> x : ys
    sby cmp = L.foldr (iby cmp) []


toList :: Map k a -> [(k,a)]
toList (Assocs kas) = kas

minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy cmp xs        =  foldl1 minBy xs
                        where
                           minBy x y = case cmp x y of
                                       GT -> y
                                       _  -> x
