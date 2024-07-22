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

id2 :: a -> a 
id2 x = x


-- type that have one type varaible
data MyList a where
  Ni :: MyList a
  Cons :: a -> MyList a -> MyList a

-- recursion on recursive GADT 
lengthList :: MyList a -> Int
lengthList Ni        = 0
lengthList (Cons _ xs) = 1 + lengthList xs


-- type that have no type variable 
data Color = Red | Green | Blue | Yellow 

instance Eq Color where
    Red == Red = True
    Green == Green = True
    Blue == Blue = True
    Yellow == Yellow = True
    _ == _ = False

complement :: Color -> Color
complement Red = Green
complement Green = Red
complement Blue = Yellow 
complement Yellow = Red

data MyBool = MyTrue | MyFalse 


checkeq :: Eq a => a -> a -> Bool
checkeq a a1 = a == a1

idlr :: Either l r -> Either l r 
idlr x = x

extractLeft :: Either a b -> Maybe a
extractLeft (Left x)  = Just x
extractLeft (Right _) = Nothing

extractRight :: Either a b -> Maybe b
extractRight (Right x)  = Just x
extractRight (Left _) = Nothing


-- Suggestion from professor William
myTuple :: (MyList a, MyList b) => a -> b -> (a, b)
myTuple x y = (x, y)

myMap :: (MyList a, MyList b) => [a] -> (a -> b) -> [b]
myMap a f = map f a 

myid :: MyList a => a -> a
myid x = x

