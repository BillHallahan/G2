module QuickSortSize (quickSort) where
    
{-@ quickSort    :: (Ord a) => xs:[a] -> { ys:[a] | len xs == len ys } @-}
quickSort :: Ord a => [a] -> [a]
quickSort [] = []
quickSort (p:xs) =
    let
        (ls, gt) = partition (< p) xs
    in
    quickSort ls `app` (p:quickSort gt)

partition          :: (a -> Bool) -> [a] -> ([a], [a])
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs

app :: [a] -> [a] -> [a]
app [] ys = ys
app xs [] = xs
app (x:xs) ys = x:app xs ys