-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined (appF, size) where

data L a = C a (L a)
         | E
         deriving (Eq, Ord, Show)

{-@ measure size @-}
size :: L a -> Int
size (C _ xs) = 1 + size xs
size E = 0

{-@ invariant {v:L a | 0 <= size v} @-}

appF :: Int
appF = f (C 1 (C 0 E)) (C 4 (C 3 E))

f :: L Int -> L Int -> Int
f x y = if size x == size y then 1 else die ""

{-@ die :: { s:String | false } -> Int @-}
die :: String -> Int
die = error