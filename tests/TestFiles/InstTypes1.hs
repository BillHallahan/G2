module InstTypes1 where

-- myFilter :: (a -> Bool) -> [a] -> [a]
-- myFilter _ [] = []
-- myFilter p (x:xs)
--   | p x       = x : myFilter p xs
--   | otherwise = myFilter p xs

-- myHead :: [a] -> a 
-- myHead [] = error "Can't find head on an empty list"
-- myHead (x : _) = x

-- myReverse :: [a] -> [a]
-- myReverse [] = []
-- myReverse (x : xs) = myReverse xs ++ [x]

-- myZip :: [a] -> [b] -> [(a,b)]
-- myZip [] _ = []
-- myZip _ [] = []
-- myZip (x : xs) (y : ys) = (x,y) : myZip xs ys

-- myIdentity :: a -> a
-- myIdentity a = a

-- returnFirst :: a -> b -> a
-- returnFirst a _ = a 

-- returnSecond :: a -> b -> b 
-- returnSecond _ b = b

-- -- focus on f a 
-- -- look at the kind of the argument and decided on how many
-- cId :: f Int -> f Int
-- cId x = x

-- compId :: f a -> f a
-- compId x = x

-- compId2 :: f a b -> f a b
-- compId2 x = x

-- data MyEither l r = MyLeft l | MyRight r

-- mkLeft :: l -> MyEither l r
-- mkLeft l = MyLeft l

-- id2 :: a -> a 
-- id2 x = x


--Actual test case that's useful

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

instance Eq a => Eq (MyList a) where
  Ni == Ni = True
  Cons x xs == Cons y ys = (x == y) && (xs == ys)
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
contains :: Eq a => a -> MyList a -> Bool
contains _ Ni = False
contains x (Cons y ys) = (x == y) || contains x ys

headMyList :: MyList a -> Maybe a
headMyList Ni = Nothing
headMyList (Cons x _) = Just x

myTuple ::  a -> b -> (a,b)
myTuple x y = (x, y)

myListTuple ::  MyList a -> MyList a -> (MyList a, MyList a)
myListTuple x y = (x, y)

myListTuple2 ::  MyList a -> MyList b -> (MyList a, MyList b)
myListTuple2 x y = (x, y)

myMap :: [a] -> (a -> b) -> [b]
myMap a f = map f a 

myListMap :: [MyList a] -> (MyList a -> MyList b) -> [MyList b]
myListMap a f = map f a 

myId :: a -> a
myId x = x

myListId :: MyList a -> MyList a 
myListId x = x

myListInt :: MyList Int -> MyList Int 
myListInt x = x

-- test cases for three arguments
data Tri a b c where
  Tri :: a -> b -> Maybe c -> Tri a b c

triFun :: Tri Int b c -> Tri b b c
triFun (Tri x y z) = Tri y y z

triInt :: Tri Int b c -> Int
triInt (Tri x y z) = x 

triFuna :: Tri a b c -> a 
triFuna (Tri x y z) = x


takeMyList :: MyList a -> MyList a -> MyList a -> MyList b -> MyList a
takeMyList x _ _ _ = x 

takeOne :: a -> a -> a -> b -> a 
takeOne x _ _ _ = x

takeb :: a -> a -> a -> b -> b
takeb _ _ _ x = x

takeTwo :: a -> a -> a -> b -> a 
takeTwo _ x _ _ = x

takeTwo2 :: a -> a -> a -> b -> c -> c 
takeTwo2 _ _ _ _ x = x


takeIntMul :: a -> a -> a -> b -> b
takeIntMul _ _ _ x = x

takeMul :: Int -> a -> a -> b -> Int
takeMul x _ _ _ = x

takeInt :: Int -> a -> b -> Int
takeInt x _ _ = x

takeIntTwo :: Int -> a -> Int
takeIntTwo x _ = x

-- take3, takeMyList, myListTuple, myListMap has a bad argument passed error 
-- however take2 with Either l r successfully work?
take3 :: Tri a b c -> Tri a b c -> Tri a b c -> Tri a b c -> Tri a b c
take3 _ _ _ x = x

take2 :: Either l r -> Either l r -> Either l r -> Either l r -> Either l r 
take2 _ _ _ x = x


data Fou a b c d where
  Fou :: a -> b -> c -> Maybe d -> Fou a b c d 

take4 :: Fou a b c d -> Fou a b c d -> Fou a b c d -> Fou a b c d -> Fou a b c d 
take4 x _ _ _ = x