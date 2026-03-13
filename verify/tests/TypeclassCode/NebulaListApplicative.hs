module TypeclassCode.NebulaListApplicative where

-- Applicative laws
pure x    = x:[]

-- GHC's base defines (<*>) on lists as:
-- @ fs <*> xs = [f x | f <- fs, x <- xs] @
-- which does not work with the custom list type we need for CycleQ.
-- The below is the result of compiling this to G2's intermediate representation,
-- lambda lifting let-bound functions, and then adapting to work with List.
--
-- With build in list type:
-- @
-- (<**>) :: forall a . forall b . [a -> b] -> [a] -> [b]
-- f <**> xs = ds'2 f xs

-- ds'2 ds1'2 xs = case ds1'2 of
--             []  -> []
--             ds3 : ds4 -> ds5 xs ds3 ds4 xs

-- ds5 ds6 ds3 ds4 xs = case ds6 of
--             []  -> ds'2 ds4 xs
--             ds8 : ds9 -> (ds3 ds8):(ds5 ds9 ds3 ds4 xs)
-- @
-- 
-- Testing with built in list type:
--      ghci> ([\x -> x + 1, \y -> y * 2, \z -> z + 7] <*> [1..10]) == ([\x -> x + 1, \y -> y * 2, \z -> z + 7] <**> [1..10])
--      True
(<*>) :: [a -> b] -> [a] -> [b]
f <*> xs = ds'2 f xs

ds'2 :: [t -> a] -> [t] -> [a]
ds'2 ds1'2 xs = case ds1'2 of
            []  -> []
            ds3 : ds4 -> ds5 xs ds3 ds4 xs

ds5 :: [t] -> (t -> a) -> [t -> a] -> [t] -> [a]
ds5 ds6 ds3 ds4 xs = case ds6 of
            []  -> ds'2 ds4 xs
            ds8 : ds9 -> (ds3 ds8):(ds5 ds9 ds3 ds4 xs)
