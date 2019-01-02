module HigherOrder where

data X = X deriving Eq

f :: X -> X
f X = X

{-@ g :: (X -> X) -> {x:X | isX x} @-}
g :: (X -> X) -> X
g h = h X

{-@ measure isX @-}
isX :: X -> Bool
isX X = False

{-@ maybeMapGt0 :: (Int -> {y:Int | y > 0 }) -> [Maybe Int] -> [Maybe {z:Int | z > 0}] @-}
maybeMapGt0 :: (Int -> Int) -> [Maybe Int] -> [Maybe Int]
maybeMapGt0 f = map (fmapIntAdding f)

{-@ fmapIntAdding :: (Int -> {y:Int | y >= 0 }) -> Maybe Int -> Maybe {z:Int | z > 0} @-}
fmapIntAdding :: (Int -> Int) -> Maybe Int -> Maybe Int
fmapIntAdding f (Just i) = Just (f i + 1)
fmapIntAdding _ Nothing = Nothing