{-# LANGUAGE AllowAmbiguousTypes, ScopedTypeVariables #-}

module TypeClasses where

import Control.Applicative
import Data.Functor.Classes

import TypeclassCode.Tree
import TypeclassCode.Reader
import TypeclassCode.State

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

monoidLeftIdentityList :: Eq a => [a] -> Bool
monoidLeftIdentityList = monoidLeftIdentity

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

-------------------------------------------------------------------------------
-- Maybe
-------------------------------------------------------------------------------

-- Maybe Monoid
monoidRightIdentityMaybe :: (Semigroup a, Eq a) => Maybe a -> Bool
monoidRightIdentityMaybe = monoidRightIdentity

monoidLeftIdentityMaybe :: (Semigroup a, Eq a) => Maybe a -> Bool
monoidLeftIdentityMaybe = monoidLeftIdentity

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

appInterchangeMaybe :: Eq b => Maybe (a -> b) -> a -> Bool
appInterchangeMaybe = appInterchange

-- Maybe Monad
monadLeftIdentityMaybe :: Eq b => a -> (a -> Maybe b) -> Bool
monadLeftIdentityMaybe = monadLeftIdentity

monadRightIdentityMaybe :: Eq b => Maybe b -> Bool
monadRightIdentityMaybe = monadRightIdentity

monadAssociativityMaybe :: Eq b => Maybe a1 -> p -> (a1 -> Maybe a2) -> (a2 -> Maybe b) -> Bool
monadAssociativityMaybe = monadAssociativity

-------------------------------------------------------------------------------
-- ZipLists
-------------------------------------------------------------------------------

appIdentityZipList :: Eq a => ZipList a -> Bool
appIdentityZipList = appIdentity

appCompositionZipList :: Eq b => ZipList (a1 -> b) -> ZipList (a2 -> a1) -> ZipList a2 -> Bool
appCompositionZipList = appComposition

appHomomorphismZipList :: Eq b => (a -> b) -> a -> Bool
appHomomorphismZipList = appHomomorphism @ZipList 

appInterchangeZipList :: Eq b => ZipList (a -> b) -> a -> Bool
appInterchangeZipList = appInterchange

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

-- Tree functo
fmapIdTree :: Eq a => Tree a -> Bool
fmapIdTree = fmapId

fmapCompositionTree :: Eq c => (b -> c) -> (a -> b) -> Tree a -> Bool
fmapCompositionTree = fmapComposition

-- Tree applicative
appIdentityTree :: Eq a => Tree a -> Bool
appIdentityTree = appIdentity

appCompositionTree :: Eq b => Tree (a1 -> b) -> Tree (a2 -> a1) -> Tree a2 -> Bool
appCompositionTree = appComposition

appHomomorphismTree :: Eq b => (a -> b) -> a -> Bool
appHomomorphismTree = appHomomorphism @Tree 

appInterchangeTree :: Eq b => Tree (a -> b) -> a -> Bool
appInterchangeTree = appInterchange

-------------------------------------------------------------------------------
-- Reader
-------------------------------------------------------------------------------

-- Reader Functor
fmapIdReader :: (Eq r, Eq a) => r -> Reader r a -> Bool
fmapIdReader r xs = runReader (fmap id xs) r == runReader (id xs) r

fmapCompositionReader :: (Eq r, Eq c) => r -> (b -> c) -> (a -> b) -> Reader r a -> Bool
fmapCompositionReader r f g xs = runReader (fmap (f . g) xs) r == runReader ((fmap f . fmap g) xs) r

-- Reader Applicative
appIdentityReader :: (Eq r, Eq a) => r -> Reader r a -> Bool
appIdentityReader r v = runReader (pure id <*> v) r == runReader v r

appCompositionReader :: (Eq r, Eq b) => r -> Reader r (a1 -> b) -> Reader r (a2 -> a1) -> Reader r a2 -> Bool
appCompositionReader r u v w = runReader (pure (.) <*> u <*> v <*> w) r == runReader (u <*> (v <*> w)) r

appHomomorphismReader :: forall r a b . (Eq r, Eq b) => r -> (a -> b) -> a -> Bool
appHomomorphismReader r f x = runReader (pure f <*> (pure :: a -> Reader r a) x) r == runReader (pure (f x)) r

appInterchangeReader :: (Eq r, Eq b) => r -> Reader r (a -> b) -> a -> Bool
appInterchangeReader r u y = runReader (u <*> pure y) r == runReader (pure ($ y) <*> u) r

-- Reader Monad
monadLeftIdentityReader :: (Eq r, Eq b) => r -> a -> (a -> Reader r b) -> Bool
monadLeftIdentityReader r a k = runReader (return a >>= k) r == runReader (k a) r

monadRightIdentityReader :: (Eq r, Eq b) => r -> Reader r b -> Bool
monadRightIdentityReader r m = runReader (m >>= return) r == runReader m r

monadAssociativityReader :: (Eq r, Eq b) => r -> Reader r a1 -> p -> (a1 -> Reader r a2) -> (a2 -> Reader r b) -> Bool
monadAssociativityReader r m x k h = runReader (m >>= (\x -> k x >>= h)) r == runReader ((m >>= k) >>= h) r

-------------------------------------------------------------------------------
-- State
-------------------------------------------------------------------------------

-- State Functor
fmapIdState :: (Eq s, Eq a) => s -> State s a -> Bool
fmapIdState s xs = runState (fmap id xs) s == runState (id xs) s

fmapCompositionState :: (Eq s, Eq c) => s -> (b -> c) -> (a -> b) -> State s a -> Bool
fmapCompositionState s f g xs = runState (fmap (f . g) xs) s == runState ((fmap f . fmap g) xs) s

-- State Applicative
appIdentityState :: (Eq s, Eq a) => s -> State s a -> Bool
appIdentityState s v = runState (pure id <*> v) s == runState v s

appCompositionState :: (Eq s, Eq b) => s -> State s (a1 -> b) -> State s (a2 -> a1) -> State s a2 -> Bool
appCompositionState s u v w = runState (pure (.) <*> u <*> v <*> w) s == runState (u <*> (v <*> w)) s

appHomomorphismState :: forall s a b . (Eq s, Eq b) => s -> (a -> b) -> a -> Bool
appHomomorphismState s f x = runState (pure f <*> (pure :: a -> State s a) x) s == runState (pure (f x)) s

appInterchangeState :: (Eq s, Eq b) => s -> State s (a -> b) -> a -> Bool
appInterchangeState s u y = runState (u <*> pure y) s == runState (pure ($ y) <*> u) s

-- State Monad
monadLeftIdentityState :: (Eq s, Eq b) => s -> a -> (a -> State s b) -> Bool
monadLeftIdentityState s a k = runState (return a >>= k) s == runState (k a) s

monadRightIdentityState :: (Eq s, Eq b) => s -> State s b -> Bool
monadRightIdentityState s m = runState (m >>= return) s == runState m s

monadAssociativityState :: (Eq s, Eq b) => s -> State s a1 -> p -> (a1 -> State s a2) -> (a2 -> State s b) -> Bool
monadAssociativityState s m x k h = runState (m >>= (\x -> k x >>= h)) s == runState ((m >>= k) >>= h) s
