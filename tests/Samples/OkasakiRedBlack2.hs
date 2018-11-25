-- Bill Hallahan
-- Based on https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/redblack99.pdf
--      and https://themonadreader.files.wordpress.com/2013/08/issue221.pdf
module RedBlack where

data Color = R | B deriving Eq
data Node a = E | N Color (Node a) a (Node a)
type Tree a = Node a

member :: Ord a => a -> Tree a -> Bool
member _ E = False
member x (N _ l y r)
    | x < y = member x l
    | x > y = member x r
    | otherwise = True

insert :: Ord a => a -> Tree a -> Tree a
insert x t = makeBlack (ins t)
    where
        ins E = N R E x E
        ins (N c l y r)
            | x < y = balance c (ins l) y r
            | x > y = balance c l y (ins r)
            | otherwise = N c l y r

        makeBlack (N _ l y r) = N B l y r

insertInt :: Int -> Tree Int -> Tree Int
insertInt = insert

assume_insert :: Int -> Tree Int -> Tree Int -> Bool
assume_insert _ t _ = inv1 t

balance :: Color -> Tree a -> a -> Tree a -> Tree a
balance B (N R (N R a x b) y c) z d = N R (N B a x b) y (N B c z d)
balance B (N R a x (N R b y c)) z d = N R (N B a x b) y (N B c z d)
balance B a x (N R (N R b y c) z d) = N R (N B a x b) y (N B c z d)
balance B a x (N R b y (N R c z d)) = N R (N B a x b) y (N B c z d)
balance c a x b = N c a x b

-- Invariant 1: No red node has a red parent
inv1 :: Tree a -> Bool
inv1 (N B t1 _ t2) = inv1 t1 && inv1 t2
inv1 (N R t1 _ t2) =
    inv1RedCh t1 && inv1RedCh t2 && inv1 t1 && inv1 t2
inv1 E = True

inv1RedCh :: Tree a -> Bool
inv1RedCh (N R _ _ _) = False
inv1RedCh _ = True

-- Invariant 2: Every path from the root to an empty node contains the same number of black nodes.
inv2 :: Tree a -> Bool
inv2 t = case blackHeight t of
    Just _ -> True
    Nothing -> False

blackHeight :: Tree a -> Maybe Int
blackHeight E = Just 0
blackHeight (N c t1 _ t2) =
    case (blackHeight t1, blackHeight t2) of
        (Just n, Just m) -> if n /= m
                                then Nothing
                                else if c == B
                                    then Just (n + 1)
                                    else Just n
        _ -> Nothing

-- Properties that can be checked with G2
prop_inv1 :: Int -> Tree Int -> Bool
prop_inv1 x t = inv1 (insert x t)

prop_inv2 :: Int -> Tree Int -> Bool
prop_inv2 x t = inv2 (insert x t)

assume_inv :: Int -> Tree Int -> Bool -> Bool
assume_inv _ t _ = inv1 t