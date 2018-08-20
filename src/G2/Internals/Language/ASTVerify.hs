-- | Defines various functions for verifying the types in an AST

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.ASTVerify (letsTypeValid) where
import G2.Internals.Language.Syntax
import G2.Internals.Language.AST
import G2.Internals.Language.Typing

-- | typeMatch
-- Checks if a typed class matches the type of another typed class
typeMatch :: (Typed a, Typed b) => a -> b -> Bool
typeMatch x y = typeOf x .::. typeOf y

-- | letsTypeValid
-- Takes an ASTContainer and returns a list of all Binds inside lets for which
-- the types were inconsistent
letsTypeValid :: (ASTContainer m Expr) => m -> Binds
letsTypeValid = evalASTs letsTypeValid'

letsTypeValid' :: Expr -> Binds
letsTypeValid' (Let bs e) = foldr bindCheckAcc [] bs
    where
    bindCheckAcc b acc = if typeMatch (fst b) (snd b) then acc else b:acc
letsTypeValid' e = []


-- | caseTypeValid
-- In all case expressions, the types of the Expr and Id, should match, and
-- they should also correspond to either the DataCon or Lit in the AltMatches.
-- Returns the App under which the case fails to typematch paired with a list of
-- pairs of expressions under that case which fails
-- caseTypeValid :: m -> [(Expr, [(Expr, Expr)])]
-- caseTypeValid = evalASTs caseTypeValid'

-- caseTypeValid' :: Expr -> [(Expr, ]
-- caseTypeValid' c@(Case e i alts) = foldr ((&&) . (typeMatch i)) (typeMatch i e) (alts)
-- caseTypeValid' e = caseTypeValid $ children e

