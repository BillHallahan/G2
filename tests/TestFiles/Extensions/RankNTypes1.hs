{-# LANGUAGE RankNTypes #-}

applyTwice :: (forall a. a -> a) -> c -> b -> (c,b)
applyTwice f c b = f (f c, f b)

-- mapTwice ::  forall a. (forall a1. Num a1 => (a1 -> a1) -> a1 -> a1) -> a -> a
-- mapTwice f x = f (f id) x

applyThenCombine :: (forall a. b -> a) -> (forall a. a -> a -> a) -> b -> b
applyThenCombine f g x = g (f x) x

applyTwiceNum :: (forall a. Num a => (forall a1. Num a1 => a1 -> a1) -> a -> a)
applyTwiceNum f x = f (f x)

tt :: Num a =>a -> a
tt x = x + x

--rankN (+1)
rankN :: (forall n. Num n => n -> n) -> (Int, Double)
rankN f = (f 1, f 1.0)

applyConcrete :: (forall a. Show a => a -> String) -> String -> String
applyConcrete f arg = f arg ++ " (applied to concrete argument)"


