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

{-@ f :: xs:L a -> { ys:L a | size xs == 0 || size ys == size xs + 2 } @-}
f :: L a -> L a
f E = E
f (C x xs) = C x (C x xs) 