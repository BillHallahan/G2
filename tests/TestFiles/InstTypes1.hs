module InstTypes1 where

myFilter :: (a -> Bool) -> [a] -> [a]
myFilter _ [] = []
myFilter p (x:xs)
  | p x       = x : myFilter p xs
  | otherwise = myFilter p xs

myHead :: [a] -> a 
myHead [] = error "Can't find head on an empty list"
myHead (x : _) = x

myReverse :: [a] -> [a]
myReverse [] = []
myReverse (x : xs) = myReverse xs ++ [x]

myZip :: [a] -> [b] -> [(a,b)]
myZip [] _ = []
myZip _ [] = []
myZip (x : xs) (y : ys) = (x,y) : myZip xs ys

myIdentity :: a -> a
myIdentity a = a

returnFirst :: a -> b -> a
returnFirst a _ = a 

returnSecond :: a -> b -> b 
returnSecond _ b = b

-- focus on f a 
-- look at the kind of the argument and decided on how many
cId :: f Int -> f Int
cId x = x

compId :: f a -> f a
compId x = x

compId2 :: f a b -> f a b
compId2 x = x

data MyEither l r = MyLeft l | MyRight r

mkLeft :: l -> MyEither l r
mkLeft l = MyLeft l