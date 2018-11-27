module BadCoerce where

data Node a = N a deriving Eq
type Tree a = Node a

f :: Tree a -> Tree a
f t = ins t
    where
        ins (N y) = N y
