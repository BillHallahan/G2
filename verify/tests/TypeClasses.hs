{-# LANGUAGE AllowAmbiguousTypes, ScopedTypeVariables #-}

module TypeClasses where

import Data.Functor.Classes

-- Monoid laws
monoidRightIdentity :: (Monoid a, Eq a) => a -> Bool
monoidRightIdentity x = x <> mempty == x

monoidLeftIdentity :: (Monoid a, Eq a) => a -> Bool
monoidLeftIdentity x = mempty <> x == x 

monoidAssociativity :: (Monoid a, Eq a) => a -> a -> a -> Bool
monoidAssociativity x y z = x <> (y <> z) == (x <> y) <> z

monoidConcatenation :: (Monoid a, Eq a) => [a] -> Bool
monoidConcatenation xs = mconcat xs == foldr (<>) mempty xs

-- Functor laws
fmapId :: (Functor f, Eq (f a)) => f a -> Bool
fmapId xs = fmap id xs == id xs

fmapComposition :: (Functor f, Eq (f c)) => (b -> c) -> (a -> b) -> f a -> Bool
fmapComposition f g xs = fmap (f . g) xs == (fmap f . fmap g) xs

-- Applicative laws
appIdentity :: (Applicative f, Eq (f a)) => f a -> Bool
appIdentity v = (pure id <*> v) == v

appComposition :: (Applicative f, Eq (f b)) => f (a1 -> b) -> f (a2 -> a1) -> f a2 -> Bool
appComposition u v w = (pure (.) <*> u <*> v <*> w) == (u <*> (v <*> w))

appHomomorphism :: forall f a b . (Applicative f, Eq (f b)) => (a -> b) -> a -> Bool
appHomomorphism f x = (pure f <*> (pure :: a -> f a) x) == pure (f x)

appInterchange :: (Eq (f b), Applicative f) => f (a -> b) -> a -> Bool
appInterchange u y = (u <*> pure y) == (pure ($ y) <*> u)

-- Monad laws
monadLeftIdentity :: (Monad m, Eq (m b)) => a -> (a -> m b) -> Bool
monadLeftIdentity a k = (return a >>= k) == k a

monadRightIdentity :: (Monad m, Eq (m b)) => m b -> Bool
monadRightIdentity m = (m >>= return) == m

monadAssociativity :: (Monad m, Eq (m b)) => m a1 -> p -> (a1 -> m a2) -> (a2 -> m b) -> Bool
monadAssociativity m x k h = (m >>= (\x -> k x >>= h)) == ((m >>= k) >>= h)

-------------------------------------------------------------------------------
-- Lists
-------------------------------------------------------------------------------
-- List Monoid
monoidRightIdentityList :: Eq a => [a] -> Bool
monoidRightIdentityList = monoidRightIdentity

monoidLeftIdentityyList :: Eq a => [a] -> Bool
monoidLeftIdentityyList = monoidLeftIdentity

monoidAssociativityList :: Eq a => [a] -> [a] -> [a] -> Bool
monoidAssociativityList = monoidAssociativity

monoidConcatenationList :: Eq a => [[a]] -> Bool
monoidConcatenationList = monoidConcatenation

-- List Functor
fmapIdList :: Eq a => [a] -> Bool
fmapIdList = fmapId

fmapCompositionList :: Eq c => (b -> c) -> (a -> b) -> [a] -> Bool
fmapCompositionList = fmapComposition

-- List Applicative
appIdentityList :: Eq a => [a] -> Bool
appIdentityList = appIdentity

appCompositionList :: Eq b => [a1 -> b] -> [a2 -> a1] -> [a2] -> Bool
appCompositionList = appComposition

appHomomorphismList :: Eq b => (a -> b) -> a -> Bool
appHomomorphismList = appHomomorphism @[] 

appInterchangeList :: Eq b => [a -> b] -> a -> Bool
appInterchangeList = appInterchange

-- List Monad
monadLeftIdentityList :: Eq b => a -> (a -> [b]) -> Bool
monadLeftIdentityList = monadLeftIdentity

monadRightIdentityList :: Eq b => [b] -> Bool
monadRightIdentityList = monadRightIdentity

monadAssociativityList :: Eq b => [a1] -> p -> (a1 -> [a2]) -> (a2 -> [b]) -> Bool
monadAssociativityList = monadAssociativity

-- Maybe Monoid
monoidRightIdentityMaybe :: (Semigroup a, Eq a) => Maybe a -> Bool
monoidRightIdentityMaybe = monoidRightIdentity

monoidLeftIdentityyMaybe :: (Semigroup a, Eq a) => Maybe a -> Bool
monoidLeftIdentityyMaybe = monoidLeftIdentity

monoidAssociativityMaybe :: (Semigroup a, Eq a) => Maybe a -> Maybe a -> Maybe a -> Bool
monoidAssociativityMaybe = monoidAssociativity

monoidConcatenationMaybe ::(Semigroup a, Eq a) =>[Maybe a] -> Bool
monoidConcatenationMaybe = monoidConcatenation

-- Maybe Functor
fmapIdMaybe :: Eq a => Maybe a -> Bool
fmapIdMaybe = fmapId

fmapCompositionMaybe :: Eq c => (b -> c) -> (a -> b) -> Maybe a -> Bool
fmapCompositionMaybe = fmapComposition

-- Maybe Applicative
appIdentityMaybe :: Eq a => Maybe a -> Bool
appIdentityMaybe = appIdentity

appCompositionMaybe :: Eq b => Maybe (a1 -> b) -> Maybe (a2 -> a1) -> Maybe a2 -> Bool
appCompositionMaybe = appComposition

appHomomorphismMaybe :: Eq b => (a -> b) -> a -> Bool
appHomomorphismMaybe = appHomomorphism @Maybe

appInterchangeMaybe :: Eq b => [a -> b] -> a -> Bool
appInterchangeMaybe = appInterchange

-- Maybe Monad
monadLeftIdentityMaybe :: Eq b => a -> (a -> Maybe b) -> Bool
monadLeftIdentityMaybe = monadLeftIdentity

monadRightIdentityMaybe :: Eq b => [b] -> Bool
monadRightIdentityMaybe = monadRightIdentity

monadAssociativityMaybe :: Eq b => Maybe a1 -> p -> (a1 -> Maybe a2) -> (a2 -> Maybe b) -> Bool
monadAssociativityMaybe = monadAssociativity