{-# LANGUAGE AllowAmbiguousTypes, LiberalTypeSynonyms, ScopedTypeVariables, TupleSections #-}
{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module TypeClasses where

import Control.Applicative
import Data.Functor.Classes
import Data.List.NonEmpty
import Data.Monoid

import TypeclassCode.Tree
import TypeclassCode.Reader
import TypeclassCode.State

import qualified TypeclassCode.NebulaListApplicative as LA
import qualified TypeclassCode.NebulaNonEmptyMonad as MN
import qualified TypeclassCode.NebulaTuple as TM

-- Semigroup laws
semigroupAssociativityLHS :: (Semigroup a, Eq a) => a -> a -> a -> a
semigroupAssociativityLHS x y z = x <> (y <> z)

semigroupAssociativityRHS :: (Semigroup a, Eq a) => a -> a -> a -> a
semigroupAssociativityRHS x y z = (x <> y) <> z

-- Monoid laws
monoidRightIdentityLHS :: (Monoid a, Eq a) => a -> a
monoidRightIdentityLHS x = x <> mempty

monoidRightIdentityRHS :: (Monoid a, Eq a) => a -> a
monoidRightIdentityRHS x = x

monoidLeftIdentityLHS :: (Monoid a, Eq a) => a -> a
monoidLeftIdentityLHS x = mempty <> x

monoidLeftIdentityRHS :: (Monoid a, Eq a) => a -> a
monoidLeftIdentityRHS x = x 

monoidConcatenationLHS :: (Monoid a, Eq a) => [a] -> a
monoidConcatenationLHS xs = mconcat xs

monoidConcatenationRHS :: (Monoid a, Eq a) => [a] -> a
monoidConcatenationRHS xs = foldr (<>) mempty xs

-- Functor laws
fmapIdLHS :: (Functor f, Eq (f Int)) => f Int -> f Int
fmapIdLHS xs = fmap id xs

fmapIdRHS :: (Functor f, Eq (f Int)) => f Int -> f Int
fmapIdRHS xs = id xs

fmapCompositionLHS :: (Functor f, Eq (f Int)) => (b -> Int) -> (a -> b) -> f a -> f Int
fmapCompositionLHS f g xs = fmap (f . g) xs

fmapCompositionRHS :: (Functor f, Eq (f Int)) => (b -> Int) -> (a -> b) -> f a -> f Int
fmapCompositionRHS f g xs = (fmap f . fmap g) xs

-- Applicative laws
appIdentityLHS :: (Eq (f Int), Applicative f) => f Int -> f Int
appIdentityLHS v = (pure id <*> v)

appIdentityRHS :: (Eq (f Int), Applicative f) => f Int -> f Int
appIdentityRHS v = v

appCompositionLHS :: (Eq (f Int), Applicative f) => f (a1 -> Int) -> f (a2 -> a1) -> f a2 -> f Int
appCompositionLHS u v w = (pure (.) <*> u <*> v <*> w)

appCompositionRHS :: (Eq (f Int), Applicative f) => f (a1 -> Int) -> f (a2 -> a1) -> f a2 -> f Int
appCompositionRHS u v w = (u <*> (v <*> w))

appHomomorphismLHS :: forall f a . (Applicative f, Eq (f Int)) => (a -> Int) -> a -> f Int
appHomomorphismLHS f x = (pure f <*> (pure :: a -> f a) x)

appHomomorphismRHS :: forall f a b . (Applicative f, Eq (f Int)) => (a -> Int) -> a -> f Int
appHomomorphismRHS f x = pure (f x)

appInterchangeLHS :: (Eq (f Int), Applicative f) => f (a -> Int) -> a -> f Int
appInterchangeLHS u y = (u <*> pure y)

appInterchangeRHS :: (Eq (f Int), Applicative f) => f (a -> Int) -> a -> f Int
appInterchangeRHS u y = (pure ($ y) <*> u)

-- Monad laws
monadLeftIdentityLHS :: (Monad m, Eq (m Int)) => a -> (a -> m Int) -> m Int
monadLeftIdentityLHS a k = (return a >>= k)

monadLeftIdentityRHS :: (Monad m, Eq (m Int)) => a -> (a -> m Int) -> m Int
monadLeftIdentityRHS a k = k a

monadRightIdentityLHS :: (Monad m, Eq (m Int)) => m Int -> m Int
monadRightIdentityLHS m = (m >>= return)

monadRightIdentityRHS :: (Monad m, Eq (m Int)) => m Int -> m Int
monadRightIdentityRHS m = m

monadAssociativityLHS :: (Monad m, Eq (m Int)) => m a1 -> p -> (a1 -> m a2) -> (a2 -> m Int) -> m Int
monadAssociativityLHS m x k h = (m >>= (\x -> k x >>= h))

monadAssociativityRHS :: (Monad m, Eq (m Int)) => m a1 -> p -> (a1 -> m a2) -> (a2 -> m Int) -> m Int
monadAssociativityRHS m x k h = ((m >>= k) >>= h)

-------------------------------------------------------------------------------
-- Lists
-------------------------------------------------------------------------------
-- List Monoid

monoidRightIdentityLHSList = monoidRightIdentityLHS @[Int]
monoidRightIdentityListRHS = monoidRightIdentityRHS @[Int]

monoidLeftIdentityLHSList = monoidLeftIdentityLHS @[Int]
monoidLeftIdentityRHSList = monoidLeftIdentityRHS @[Int]

semigroupAssociativityLHSList = semigroupAssociativityLHS @[Int]
semigroupAssociativityRHSList = semigroupAssociativityRHS @[Int]

monoidConcatenationLHSList = monoidConcatenationLHS @[Int]
monoidConcatenationRHSList = monoidConcatenationRHS @[Int]

fmapIdLHSList xs = fmapIdLHS @[]
fmapIdRHSList xs = fmapIdRHS @[]

fmapCompositionLHSList = fmapCompositionLHS @[]
fmapCompositionRHSList = fmapCompositionRHS @[]


appIdentityLHSList v = LA.pure id LA.<*> v
appIdentityRHSList v = v

appCompositionLHSList u v w = (LA.pure (.) LA.<*> u LA.<*> v LA.<*> w)
appCompositionRHSList u v w = (u LA.<*> (v LA.<*> w))

appHomomorphismLHSList f x = (LA.pure f LA.<*> (LA.pure :: a -> [a]) x)
appHomomorphismRHSList f x = LA.pure (f x)

appInterchangeLHSList u y = (u LA.<*> LA.pure y)
appInterchangeRHSList u y = (LA.pure ($ y) LA.<*> u)

monadLeftIdentityLHSList = monadLeftIdentityLHS @[]
monadLeftIdentityRHSList = monadLeftIdentityRHS @[]

monadRightIdentityLHSList = monadRightIdentityLHS @[]
monadRightIdentityRHSList = monadRightIdentityRHS @[]

monadAssociativityLHSList = monadAssociativityLHS @[]
monadAssociativityRHSList = monadAssociativityRHS @[]

{-# RULES
"monoidRightIdentityList" forall . monoidRightIdentityLHSList = monoidRightIdentityListRHS
"monoidLeftIdentityList" forall . monoidLeftIdentityLHSList = monoidLeftIdentityRHSList
"semigroupAssociativityList" forall . semigroupAssociativityLHSList = semigroupAssociativityRHSList
"monoidConcatenationList" forall . monoidConcatenationLHSList = monoidConcatenationRHSList

"fmapIdList" forall xs . fmapIdLHSList xs = fmapIdRHSList xs
"fmapCompositionList" forall . fmapCompositionLHSList = fmapCompositionRHSList

"appIdentityList" forall . appIdentityLHSList = appIdentityRHSList
"appCompositionList" forall . appCompositionLHSList = appCompositionRHSList
"appHomomorphismList" forall . appHomomorphismLHSList = appHomomorphismRHSList
"appInterchangeList" forall . appInterchangeLHSList = appInterchangeRHSList

"monadLeftIdentityList" forall . monadLeftIdentityLHSList = monadLeftIdentityRHSList
"monadRightIdentityList" forall . monadRightIdentityLHSList = monadRightIdentityRHSList
"monadAssociativityList" forall . monadAssociativityLHSList = monadAssociativityRHS
#-}

-------------------------------------------------------------------------------
-- NonEmpty
-------------------------------------------------------------------------------

semigroupAssociativityLHSNonEmpty = semigroupAssociativityLHS @(NonEmpty Int)
semigroupAssociativityRHSNonEmpty = semigroupAssociativityRHS @(NonEmpty Int)

fmapIdLHSNonEmpty xs = fmapIdLHS @NonEmpty
fmapIdRHSNonEmpty xs = fmapIdRHS @NonEmpty

fmapCompositionLHSNonEmpty = fmapCompositionLHS @NonEmpty
fmapCompositionRHSNonEmpty = fmapCompositionRHS @NonEmpty

appIdentityLHSNonEmpty = appIdentityLHS @NonEmpty
appIdentityRHSNonEmpty = appIdentityRHS @NonEmpty

appCompositionLHSNonEmpty = appCompositionLHS @NonEmpty
appCompositionRHSNonEmpty = appCompositionRHS @NonEmpty

appHomomorphismLHSNonEmpty = appHomomorphismLHS @NonEmpty
appHomomorphismRHSNonEmpty = appHomomorphismRHS @NonEmpty

appInterchangeLHSNonEmpty = appInterchangeLHS @NonEmpty
appInterchangeRHSNonEmpty = appInterchangeRHS @NonEmpty

monadLeftIdentityLHSNonEmpty = monadLeftIdentityLHS @NonEmpty
monadLeftIdentityRHSNonEmpty = monadLeftIdentityRHS @NonEmpty

monadRightIdentityLHSNonEmpty m = (m MN.>>== MN.return)
monadRightIdentityRHSNonEmpty m = m

monadAssociativityLHSNonEmpty = monadAssociativityLHS @NonEmpty
monadAssociativityRHSNonEmpty = monadAssociativityRHS @NonEmpty

{-# RULES
"semigroupAssociativityNonEmpty" forall . semigroupAssociativityLHSNonEmpty = semigroupAssociativityRHSNonEmpty

"fmapIdNonEmpty" forall xs . fmapIdLHSNonEmpty xs = fmapIdRHSNonEmpty xs
"fmapCompositionNonEmpty" forall . fmapCompositionLHSNonEmpty = fmapCompositionRHSNonEmpty

"appIdentityNonEmpty" forall . appIdentityLHSNonEmpty = appIdentityRHSNonEmpty
"appCompositionNonEmpty" forall . appCompositionLHSNonEmpty = appCompositionRHSNonEmpty
"appHomomorphismNonEmpty" forall . appHomomorphismLHSNonEmpty = appHomomorphismRHSNonEmpty
"appInterchangeNonEmpty" forall . appInterchangeLHSNonEmpty = appInterchangeRHSNonEmpty

"monadLeftIdentityNonEmpty" forall . monadLeftIdentityLHSNonEmpty = monadLeftIdentityRHSNonEmpty
"monadRightIdentityNonEmpty" forall . monadRightIdentityLHSNonEmpty = monadRightIdentityRHSNonEmpty
"monadAssociativityNonEmpty" forall . monadAssociativityLHSNonEmpty = monadAssociativityRHS
#-}

-------------------------------------------------------------------------------
-- Maybe
-------------------------------------------------------------------------------

monoidRightIdentityLHSMaybe = monoidRightIdentityLHS @(Maybe ())
monoidRightIdentityMaybeRHS = monoidRightIdentityRHS @(Maybe ())

monoidLeftIdentityLHSMaybe = monoidLeftIdentityLHS @(Maybe ())
monoidLeftIdentityRHSMaybe = monoidLeftIdentityRHS @(Maybe ())

semigroupAssociativityLHSMaybe = semigroupAssociativityLHS @(Maybe ())
semigroupAssociativityRHSMaybe = semigroupAssociativityRHS @(Maybe ())

monoidConcatenationLHSMaybe = monoidConcatenationLHS @(Maybe ())
monoidConcatenationRHSMaybe = monoidConcatenationRHS @(Maybe ())

fmapIdLHSMaybe xs = fmapIdLHS @Maybe
fmapIdRHSMaybe xs = fmapIdRHS @Maybe

fmapCompositionLHSMaybe = fmapCompositionLHS @Maybe
fmapCompositionRHSMaybe = fmapCompositionRHS @Maybe

appIdentityLHSMaybe = appIdentityLHS @Maybe
appIdentityRHSMaybe = appIdentityRHS @Maybe

appCompositionLHSMaybe = appCompositionLHS @Maybe
appCompositionRHSMaybe = appCompositionRHS @Maybe

appHomomorphismLHSMaybe = appHomomorphismLHS @Maybe
appHomomorphismRHSMaybe = appHomomorphismRHS @Maybe

appInterchangeLHSMaybe = appInterchangeLHS @Maybe
appInterchangeRHSMaybe = appInterchangeRHS @Maybe

monadLeftIdentityLHSMaybe = monadLeftIdentityLHS @Maybe
monadLeftIdentityRHSMaybe = monadLeftIdentityRHS @Maybe

monadRightIdentityLHSMaybe = monadRightIdentityLHS @Maybe
monadRightIdentityRHSMaybe = monadRightIdentityRHS @Maybe

monadAssociativityLHSMaybe = monadAssociativityLHS @Maybe
monadAssociativityRHSMaybe = monadAssociativityRHS @Maybe

{-# RULES
"monoidRightIdentityMaybe" forall . monoidRightIdentityLHSMaybe = monoidRightIdentityMaybeRHS
"monoidLeftIdentityMaybe" forall . monoidLeftIdentityLHSMaybe = monoidLeftIdentityRHSMaybe
"semigroupAssociativityMaybe" forall . semigroupAssociativityLHSMaybe = semigroupAssociativityRHSMaybe
"monoidConcatenationMaybe" forall . monoidConcatenationLHSMaybe = monoidConcatenationRHSMaybe

"fmapIdMaybe" forall xs . fmapIdLHSMaybe xs = fmapIdRHSMaybe xs
"fmapCompositionMaybe" forall . fmapCompositionLHSMaybe = fmapCompositionRHSMaybe

"appIdentityMaybe" forall . appIdentityLHSMaybe = appIdentityRHSMaybe
"appCompositionMaybe" forall . appCompositionLHSMaybe = appCompositionRHSMaybe
"appHomomorphismMaybe" forall . appHomomorphismLHSMaybe = appHomomorphismRHSMaybe
"appInterchangeMaybe" forall . appInterchangeLHSMaybe = appInterchangeRHSMaybe

"monadLeftIdentityMaybe" forall . monadLeftIdentityLHSMaybe = monadLeftIdentityRHSMaybe
"monadRightIdentityMaybe" forall . monadRightIdentityLHSMaybe = monadRightIdentityRHSMaybe
"monadAssociativityMaybe" forall . monadAssociativityLHSMaybe = monadAssociativityRHS
#-}

-------------------------------------------------------------------------------
-- ZipLists
-------------------------------------------------------------------------------

appIdentityLHSZipList = appIdentityLHS @ZipList
appIdentityRHSZipList = appIdentityRHS @ZipList

appCompositionLHSZipList = appCompositionLHS @ZipList
appCompositionRHSZipList = appCompositionRHS @ZipList

appHomomorphismLHSZipList = appHomomorphismLHS @ZipList
appHomomorphismRHSZipList = appHomomorphismRHS @ZipList

appInterchangeLHSZipList = appInterchangeLHS @ZipList
appInterchangeRHSZipList = appInterchangeRHS @ZipList

{-# RULES
"appIdentityZipList" forall . appIdentityLHSZipList = appIdentityRHSZipList
"appCompositionZipList" forall . appCompositionLHSZipList = appCompositionRHSZipList
"appHomomorphismZipList" forall . appHomomorphismLHSZipList = appHomomorphismRHSZipList
"appInterchangeZipList" forall . appInterchangeLHSZipList = appInterchangeRHSZipList
#-}

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

fmapIdLHSTree xs = fmapIdLHS @Tree
fmapIdRHSTree xs = fmapIdRHS @Tree

fmapCompositionLHSTree = fmapCompositionLHS @Tree
fmapCompositionRHSTree = fmapCompositionRHS @Tree

appIdentityLHSTree = appIdentityLHS @Tree
appIdentityRHSTree = appIdentityRHS @Tree

appCompositionLHSTree = appCompositionLHS @Tree
appCompositionRHSTree = appCompositionRHS @Tree

appHomomorphismLHSTree = appHomomorphismLHS @Tree
appHomomorphismRHSTree = appHomomorphismRHS @Tree

appInterchangeLHSTree = appInterchangeLHS @Tree
appInterchangeRHSTree = appInterchangeRHS @Tree

{-# RULES
"fmapIdTree" forall xs . fmapIdLHSTree xs = fmapIdRHSTree xs
"fmapCompositionTree" forall . fmapCompositionLHSTree = fmapCompositionRHSTree

"appIdentityTree" forall . appIdentityLHSTree = appIdentityRHSTree
"appCompositionTree" forall . appCompositionLHSTree = appCompositionRHSTree
"appHomomorphismTree" forall . appHomomorphismLHSTree = appHomomorphismRHSTree
"appInterchangeTree" forall . appInterchangeLHSTree = appInterchangeRHSTree
#-}
-------------------------------------------------------------------------------
-- Reader
-------------------------------------------------------------------------------

-- Reader Functor
fmapIdLHSReader r xs = runReader (fmap id xs) r
fmapIdRHSReader r xs = runReader (id xs) r

fmapCompositionLHSReader r f g xs = runReader (fmap (f . g) xs) r
fmapCompositionRHSReader r f g xs = runReader ((fmap f . fmap g) xs) r

-- Reader Applicative
appIdentityReaderLHS r v = runReader (pure id <*> v) r
appIdentityReaderRHS r v = runReader v r

appCompositionReaderLHS r u v w = runReader (pure (.) <*> u <*> v <*> w) r
appCompositionReaderRHS r u v w = runReader (u <*> (v <*> w)) r

appHomomorphismReaderLHS r f x = runReader (pure f <*> (pure :: a -> Reader r a) x) r
appHomomorphismReaderRHS r f x = runReader (pure (f x)) r

appInterchangeReaderLHS r u y = runReader (u <*> pure y) r
appInterchangeReaderRHS r u y = runReader (pure ($ y) <*> u) r

-- Reader Monad
monadLeftIdentityReaderLHS r a k = runReader (return a >>= k) r
monadLeftIdentityReaderRHS r a k = runReader (k a) r

monadRightIdentityReaderLHS r m = runReader (m >>= return) r
monadRightIdentityReaderRHS r m = runReader m r

monadAssociativityReaderLHS r m x k h = runReader (m >>= (\x -> k x >>= h)) r
monadAssociativityReaderRHS r m x k h = runReader ((m >>= k) >>= h) r

{-# RULES
"fmapIdReader" forall . fmapIdLHSReader = fmapIdRHSReader
"fmapCompositionReader" forall . fmapCompositionLHSReader = fmapCompositionRHSReader

"appIdentityReader" forall . appIdentityReaderLHS = appIdentityReaderRHS
"appCompositionReader" forall . appCompositionReaderLHS = appCompositionReaderRHS
"appHomomorphismReader" forall . appHomomorphismReaderLHS = appHomomorphismReaderRHS
"appInterchangeReader" forall . appInterchangeReaderLHS = appInterchangeReaderRHS

"monadLeftIdentityReader" forall . monadLeftIdentityReaderLHS = monadLeftIdentityReaderRHS
"monadRightIdentityReader" forall . monadRightIdentityReaderLHS = monadRightIdentityReaderRHS
"monadAssociativityReader" forall . monadAssociativityReaderLHS = monadAssociativityReaderRHS
#-}
-------------------------------------------------------------------------------
-- State
-------------------------------------------------------------------------------

-- State Functor
fmapIdLHSState r xs = runState (fmap id xs) r
fmapIdRHSState r xs = runState (id xs) r

fmapCompositionLHSState r f g xs = runState (fmap (f . g) xs) r
fmapCompositionRHSState r f g xs = runState ((fmap f . fmap g) xs) r

-- State Applicative
appIdentityStateLHS r v = runState (pure id <*> v) r
appIdentityStateRHS r v = runState v r

appCompositionStateLHS r u v w = runState (pure (.) <*> u <*> v <*> w) r
appCompositionStateRHS r u v w = runState (u <*> (v <*> w)) r

appHomomorphismStateLHS r f x = runState (pure f <*> (pure :: a -> State r a) x) r
appHomomorphismStateRHS r f x = runState (pure (f x)) r

appInterchangeStateLHS r u y = runState (u <*> pure y) r
appInterchangeStateRHS r u y = runState (pure ($ y) <*> u) r

-- State Monad
monadLeftIdentityStateLHS r a k = runState (return a >>= k) r
monadLeftIdentityStateRHS r a k = runState (k a) r

monadRightIdentityStateLHS r m = runState (m >>= return) r
monadRightIdentityStateRHS r m = runState m r

monadAssociativityStateLHS r m x k h = runState (m >>= (\x -> k x >>= h)) r
monadAssociativityStateRHS r m x k h = runState ((m >>= k) >>= h) r

{-# RULES
"fmapIdState" forall . fmapIdLHSState = fmapIdRHSState
"fmapCompositionState" forall . fmapCompositionLHSState = fmapCompositionRHSState

"appIdentityState" forall . appIdentityStateLHS = appIdentityStateRHS
"appCompositionState" forall . appCompositionStateLHS = appCompositionStateRHS
"appHomomorphismState" forall . appHomomorphismStateLHS = appHomomorphismStateRHS
"appInterchangeState" forall . appInterchangeStateLHS = appInterchangeStateRHS

"monadLeftIdentityState" forall . monadLeftIdentityStateLHS = monadLeftIdentityStateRHS
"monadRightIdentityState" forall . monadRightIdentityStateLHS = monadRightIdentityStateRHS
"monadAssociativityState" forall . monadAssociativityStateLHS = monadAssociativityStateRHS
#-}

-------------------------------------------------------------------------------
-- Function
-------------------------------------------------------------------------------

-- Semigroup Function (Endo)
semigroupAssociativityFunctionLHS e f g h = appEndo (Endo f <> (Endo g <> Endo h)) e
semigroupAssociativityFunctionRHS e f g h = appEndo ((Endo f <> Endo g) <> Endo h) e

-- Function Functor
fmapIdFunctionLHS e f = (fmap id f) e
fmapIdFunctionRHS e f = (id f) e

fmapCompositionFunctionLHS e f g xs = (fmap (f . g) xs) e
fmapCompositionFunctionRHS e f g xs = ((fmap f . fmap g) xs) e

-- Function Applicative
appIdentityFunctionLHS e v = (pure id <*> v) e
appIdentityFunctionRHS e v = v e

appCompositionFunctionLHS e u v w = (pure (.) <*> u <*> v <*> w) e
appCompositionFunctionRHS e u v w =  (u <*> (v <*> w)) e

appHomomorphismFunctionLHS e f x = (pure f <*> (pure :: a -> (e -> a)) x) e
appHomomorphismFunctionRHS e f x = (pure (f x)) e

appInterchangeFunctionLHS e u y = (u <*> pure y) e
appInterchangeFunctionRHS e u y = (pure ($ y) <*> u) e

-- Function Monad
monadLeftIdentityFunctionLHS e a k = (return a >>= k) e
monadLeftIdentityFunctionRHS e a k = (k a) e

monadRightIdentityFunctionLHS e m = ((m >>= return) e)
monadRightIdentityFunctionRHS e m = m e

monadAssociativityFunctionLHS e m x k h = (m >>= (\x -> k x >>= h)) e
monadAssociativityFunctionRHS e m x k h = ((m >>= k) >>= h) e

{-# RULES
"semigroupAssociativityFunction" forall . semigroupAssociativityFunctionLHS = semigroupAssociativityFunctionRHS

"fmapIdFunction" forall . fmapIdFunctionLHS = fmapIdFunctionRHS
"fmapCompositionFunction" forall . fmapCompositionFunctionLHS = fmapCompositionFunctionRHS

"appIdentityFunction" forall . appIdentityFunctionLHS = appIdentityFunctionRHS
"appCompositionFunction" forall . appCompositionFunctionLHS = appCompositionFunctionRHS
"appHomomorphismFunction" forall . appHomomorphismFunctionLHS = appHomomorphismFunctionRHS
"appInterchangeFunction" forall . appInterchangeFunctionLHS = appInterchangeFunctionRHS

"monadLeftIdentityFunction" forall . monadLeftIdentityFunctionLHS = monadLeftIdentityFunctionRHS
"monadRightIdentityFunction" forall . monadRightIdentityFunctionLHS = monadRightIdentityFunctionRHS
"monadAssociativityFunction" forall . monadAssociativityFunctionLHS = monadAssociativityFunctionRHS
#-}

-------------------------------------------------------------------------------
-- Tuple
-------------------------------------------------------------------------------

-- Tuple Monoid
monoidRightIdentityLHSTuple x = x TM.<> TM.mempty
monoidRightIdentityTupleRHS x = x

monoidLeftIdentityLHSTuple x = TM.mempty TM.<> x
monoidLeftIdentityRHSTuple x = x

semigroupAssociativityLHSTuple = semigroupAssociativityLHS @(Sum Int, Sum Int)
semigroupAssociativityRHSTuple = semigroupAssociativityRHS @(Sum Int, Sum Int)

monoidConcatenationLHSTuple xs = TM.mconcat xs
monoidConcatenationRHSTuple xs = TM.foldr (TM.<>) TM.mempty xs

-- Tuple Functor
fmapIdLHSTuple :: Eq b => (b, Int) -> (b, Int)
fmapIdLHSTuple = fmapIdLHS
fmapIdRHSTuple :: Eq b => (b, Int) -> (b, Int)
fmapIdRHSTuple = fmapIdRHS

fmapCompositionLHSTuple :: Eq e => (b -> Int) -> (a -> b) -> (e, a) -> (e, Int)
fmapCompositionLHSTuple = fmapCompositionLHS
fmapCompositionRHSTuple :: Eq e => (b -> Int) -> (a -> b) -> (e, a) -> (e, Int)
fmapCompositionRHSTuple = fmapCompositionRHS

-- Tuple applicative
appIdentityLHSTuple = appIdentityLHS @((,) (Sum Int))
appIdentityRHSTuple = appIdentityRHS @((,) (Sum Int))

appCompositionLHSTuple u v w = (TM.pure (.) TM.<*> u TM.<*> v TM.<*> w)
appCompositionRHSTuple u v w = (u TM.<*> (v TM.<*> w))

appHomomorphismLHSTuple = appHomomorphismLHS @((,) (Sum Int))
appHomomorphismRHSTuple = appHomomorphismRHS @((,) (Sum Int))

appInterchangeLHSTuple = appInterchangeLHS @((,) (Sum Int))
appInterchangeRHSTuple = appInterchangeRHS @((,) (Sum Int))

-- Tuple Monad
monadLeftIdentityLHSTuple = monadLeftIdentityLHS @((,) (Sum Int))
monadLeftIdentityRHSTuple = monadLeftIdentityRHS @((,) (Sum Int))

monadRightIdentityLHSTuple = monadRightIdentityLHS @((,) (Sum Int))
monadRightIdentityRHSTuple = monadRightIdentityRHS @((,) (Sum Int))

monadAssociativityLHSTuple = monadAssociativityLHS @((,) (Sum Int))
monadAssociativityRHSTuple = monadAssociativityRHS @((,) (Sum Int))

{-# RULES
"monoidRightIdentityTuple" forall . monoidRightIdentityLHSTuple = monoidRightIdentityTupleRHS
"monoidLeftIdentityTuple" forall . monoidLeftIdentityLHSTuple = monoidLeftIdentityRHSTuple
"semigroupAssociativityTuple" forall . semigroupAssociativityLHSTuple = semigroupAssociativityRHSTuple
"monoidConcatenationTuple" forall . monoidConcatenationLHSTuple = monoidConcatenationRHSTuple

"fmapIdTuple" forall . fmapIdLHSTuple = fmapIdRHSTuple
"fmapCompositionTuple" forall . fmapCompositionLHSTuple = fmapCompositionRHSTuple

"appIdentityTuple" forall . appIdentityLHSTuple = appIdentityRHSTuple
"appCompositionTuple" forall . appCompositionLHSTuple = appCompositionRHSTuple
"appHomomorphismTuple" forall . appHomomorphismLHSTuple = appHomomorphismRHSTuple
"appInterchangeTuple" forall . appInterchangeLHSTuple = appInterchangeRHSTuple

"monadLeftIdentityTuple" forall . monadLeftIdentityLHSTuple = monadLeftIdentityRHSTuple
"monadRightIdentityTuple" forall . monadRightIdentityLHSTuple = monadRightIdentityRHSTuple
"monadAssociativityTuple" forall . monadAssociativityLHSTuple = monadAssociativityRHS

#-}