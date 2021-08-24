module ZipUnlessEmpty (test1, test2, test3) where

import Prelude hiding (zipWith)

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zipWith (,) xs ys

zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] []         = []
zipWith _ _  _          = die "no other cases"

{-@ test1 :: {v: _ | len v = 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | len v = 0} @-}
test2     = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | len v = 0} @-}
test3     = zipOrNull ["cat", "dog"] []