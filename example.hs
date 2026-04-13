import Data.Set as S

-- Merges all nested containers. Elements can be lost.
class (Collapseable c a) where
    collapse :: c (c a) -> c a

instance {-# OVERLAPPING #-} (Ord a) => Collapseable Set a where
    collapse ss = S.unions $ S.toList ss

instance Flattenable c => Collapseable c a where
    collapse = flatten

-- Merges all nested containers without loss of elements.
class Flattenable c where
    flatten :: c (c a) -> c a

instance Flattenable [] where
    flatten [] = []
    flatten (l:ls) = l ++ (flatten ls)

instance Flattenable Maybe where
    flatten (Just Nothing) = Nothing
    flatten (Just (Just x)) = Just x
    flatten Nothing = Nothing

test :: [Bool]
test = collapse [[True], [False, True]]

test2 :: Maybe Bool
test2 = collapse (Just Nothing)

test3 :: [Int] 
test3 = collapse [[1,2,3], [4,5,6]] 

test4 :: Set Float
test4 = collapse $ S.fromList [S.fromList [1.0,2.0], S.fromList[1.0,3.0]]