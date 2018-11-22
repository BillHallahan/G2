module BadCoerce where

data Node a = N a
type Tree a = Node a

f :: Tree a -> Tree a
f t = ins t
    where
        ins (N y) = N y