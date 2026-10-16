{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- Used to compare Nebula to Nova- Nebula crashes when run directly with the list Applicative typeclass instance,
-- but can work (not crash) on this file.

module TypeclassCode.NebulaNonEmptySemigroupAssociativity where

import Prelude (Bool (..))

data List a = a :> List a | Nil
infixl 4 :>

data NonEmpty a = a :| List a

infixr 5 :|

(++) :: List a -> List a -> List a
(++) Nil     ys = ys
(++) (x :> xs) ys = x :> (xs ++ ys)

(a :| as) <> ~(b :| bs) = a :| (as ++ (b :> bs))
