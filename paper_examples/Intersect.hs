module Intersect where

import Prelude hiding (any)

-- Example from Section 2.1 in the paper.
-- intersect_prop is a (incorrect) property to be tested about intersect.
-- By running G2 on intersect_prop with the extra flag --returns-true,
-- a counterexample can be found.

intersect_prop :: Eq a => [a] -> [a] -> Bool
intersect_prop xs ys = xs `intersect` ys == ys `intersect` xs

intersect :: Eq a => [a] -> [a] -> [a]
intersect xs ys = [x|x <- xs, any (x ==) ys]

any :: (a -> Bool) -> [a] -> Bool
any _ [] = False
any p (x:xs) = p x || any p xs
