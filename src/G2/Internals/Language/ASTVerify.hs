-- | Defines various functions for verifying the types in an AST

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.ASTVerify (letsTypeValid, caseTypeValid) where
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
letsTypeValid' (Let bs _) = filter (\b -> not $ typeMatch (fst b) (snd b)) bs
letsTypeValid' _ = []


-- | caseTypeValid
-- In all case expressions, the types of the Expr and Id, should match, and
-- they should also correspond to either the DataCon or Lit in the AltMatches.
caseTypeValid :: (ASTContainer m Expr) => m -> [(Id, Either Expr Alt)]
caseTypeValid = evalASTs caseTypeValid'

caseTypeValid' :: Expr -> [(Id, Either Expr Alt)]
caseTypeValid' (Case e i alts) = concat [[ (i, Left e) | typeMatch i e ] , altMisMatches]
  where
    -- Filter alts by AltMatch not matching the Id of the case, then pair with Id
    altMisMatches = map (\a -> (i,(Right a))) (filter (\(Alt am _) -> (not $ typeMatch am i)) alts)
caseTypeValid' _ = []

