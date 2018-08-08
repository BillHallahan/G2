-- | Defines various functions for verifying the types in an AST

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.ASTVerify (letsTypeValid, caseTypeValid) where
import G2.Internals.Language.Syntax
import G2.Internals.Language.AST
import G2.Internals.Language.Typing
import G2.Internals.Language

-- | checkProperties
-- TODO: Top-level function which handles checking properties of the AST for
-- validity.

-- | ErrorSource
-- TODO: Container for various type errors; function paired with data on what
-- errored?

-- | typeMatch
-- Checks if a typed class matches the type of another typed class
typeMatch :: (Typed a, Typed b) => a -> b -> Bool
typeMatch x y = typeOf x == typeOf y

-- | letsTypeValid
-- All Ids bound in Let statements should have the same type as the expression
-- they are bound to.
-- TODO:
--  Convert this bool into a monoid
--  Returning a list of ErrorSource ...
--      (list of the functions the Let's were in, along with the
--       Id and Expr with non-matching types.)
letsTypeValid :: (ASTContainer m Expr) => m -> Bool
letsTypeValid = evalASTs letsTypeValid'

letsTypeValid' :: Expr -> Bool
letsTypeValid' (Let bs e) = (foldr ((&&) . \x -> typeMatch (fst x) (snd x)) True bs)
letsTypeValid' e = letsTypeValid $ children e

-- | caseTypeValid
-- In all case expressions, the types of the Expr and Id, should match, and
-- they should also correspond to either the DataCon or Lit in the AltMatches.
-- caseTypeValid :: m -> Bool
-- caseTypeValid = evalASTs caseTypeValid'
--
-- caseTypeValid' :: Expr -> Bool
-- caseTypeValid' c@(Case e i alts) =  foldr ((&&) . (typeMatch i)) (typeMatch i e) (map typeOf alts)
-- caseTypeValid' e = caseTypeValid $ children e

