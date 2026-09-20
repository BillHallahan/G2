-- List monad laws
-- From TIP: https://github.com/tip-org/benchmarks/blob/master/original/tip2015/ListMonad.hs
module ListMonad where

import Prelude hiding ((>>=), return, map, concat)
import G2.Plugin

{-# ANN module ("--smt-tuples --higher-order uninterpreted --smt cvc5,z3 --time 90")
    #-}

(===) :: Eq a => a -> a -> Bool
x === y = x == y

{-# ANN (>>=) (SMTEquivIs "$>>=") #-}
(>>=) :: [a] -> (a -> [b]) -> [b]
(x:xs) >>= f = f x ++ (xs >>= f)
[]     >>= f = []

($>>=) :: [a] -> (a -> [b]) -> [b]
xs $>>= f = smtConcat (smtMap f xs)

{-# ANN weird_concat (SMTEquivIsWithConfig "weird_concatSMT" "--no-term-check")
    #-}
weird_concat :: [[a]] -> [a]
weird_concat ((x:xs):xss) = x:weird_concat (xs:xss)
weird_concat ([]:xss)     = weird_concat xss
weird_concat []           = []

weird_concatSMT :: [[a]] -> [a]
weird_concatSMT = smtConcat

{-# ANN map (SMTEquivIs "mapSMT") #-}
map :: (a -> b) -> [a] -> [b]
map f [] = []
map f (x:xs) = (f x) : (map f xs)

mapSMT :: (a -> b) -> [a] -> [b]
mapSMT = smtMap

{-# ANN concat (SMTEquivIs "concatSMT") #-}
concat :: [[a]] -> [a]
concat (x:xs) = x ++ concat xs
concat []           = []

concatSMT :: [[a]] -> [a]
concatSMT = smtConcat

-- Here, weird_concat is a somewhat sensible concateIntion function,
-- and has a somewhat strange recursion pattern.
{-# ANN prop_weird_is_normal Prop #-}
prop_weird_is_normal :: Eq a => [[a]] -> Bool
prop_weird_is_normal xs = concat xs === weird_concat xs

{-# ANN prop_weird_concat_map_bind Prop #-}
prop_weird_concat_map_bind :: Eq b => (a -> [b]) -> [a] -> Bool
prop_weird_concat_map_bind f xs = weird_concat (map f xs) === (xs >>= f)

{-# ANN prop_concat_map_bind Prop #-}
prop_concat_map_bind :: Eq b => (a -> [b]) -> [a] -> Bool
prop_concat_map_bind f xs = concat (map f xs) === (xs >>= f)

{-# ANN prop_assoc Prop #-}
prop_assoc :: Eq c => [a] -> (a -> [b]) -> (b -> [c]) -> Bool
prop_assoc m f g = ((m >>= f) >>= g) === (m >>= (\x -> f x >>= g))

{-# ANN prop_return_1 Prop #-}
prop_return_1 :: Eq b => a -> (a -> [b]) -> Bool
prop_return_1 x f = return x >>= f === f x

{-# ANN prop_return_2 Prop #-}
prop_return_2 :: Eq a => [a] -> Bool
prop_return_2 xs = xs >>= return === xs

return :: a -> [a]
return x = [x]