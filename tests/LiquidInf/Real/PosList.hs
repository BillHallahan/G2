-- cmd_line = (--no-keep_quals)

{-@ LIQUID "--no-termination" @-}

module PosList () where
	
data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ filterAndSum :: List { x:Int | x >= 0 } -> { y:Int | y >= 0  } @-}
filterAndSum :: List Int -> Int
filterAndSum xs = sumList (filterPos xs)

sumList :: List Int -> Int
sumList Emp = 0
sumList (x :+: xs) = x + sumList xs

filterPos :: List Int -> List Int
filterPos Emp = Emp
filterPos (x :+: xs)
    | x >= 0 =  x :+: filterPos xs
    | otherwise = filterPos xs