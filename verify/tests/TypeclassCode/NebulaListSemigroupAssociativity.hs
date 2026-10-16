{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- Used to compare Nebula to Nova- Nebula crashes when run directly with the list Applicative typeclass instance,
-- but can work (not crash) on this file.

module TypeclassCode.NebulaListSemigroupAssociativity where

import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)
