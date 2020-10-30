-- cmd_line = (--no-keep-quals)

{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined where


data L a = C a (L a)
         | E
         deriving (Eq, Ord, Show)

{-@ measure size @-}
size :: L a -> Int
size (C _ xs) = 1 + size xs
size E = 0

hd :: L a -> a
hd (C x _) = x
hd E = die "hd: empty list"

{-@ die :: { _:String | false } -> a @-}
die :: String -> a
die s = error s