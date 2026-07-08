module UncurryHigherOrder where

prop :: (Int -> Int -> Int) -> Int -> Bool
prop h x = (h 1 x) == uncurry h (0, x)