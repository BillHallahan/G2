
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( centroid) where

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

divide :: Double -> Int -> Double
divide n 0 = die "oops divide by zero"
divide n d = n / (fromIntegral d)

{-@ centroid :: (Double) -> Int -> rs : (Double) @-}
centroid :: Double -> Int -> Double
centroid p sz = p `divide` sz
