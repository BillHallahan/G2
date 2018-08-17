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

-- | bindsTypeValid
-- Takes a list of Binds and returns those which have invalid types
bindsTypeValid :: Binds -> Binds
bindsTypeValid bs = foldr bindCheckAcc [] bs
    where
    bindCheckAcc b acc = if typeMatch (fst b) (snd b) then acc else b:acc

-- | letsTypeValid
-- Takes an ASTContainer and returns a list of all the Lets for which the
-- types were invalid, paired with the most Recent App in which they occurred
letsTypeValid :: (ASTContainer m Expr) => m -> [(Expr,Binds)]
letsTypeValid = evalContainedASTs (letsTypeValid' Nothing)

letsTypeValid' :: Maybe Expr -> Expr -> [(Expr, Binds)]
letsTypeValid' (Just a) (Let bs e) = case badBinds of
    [] -> []
    _  -> (letsTypeValid' (Just a) e) ++ [(a,badBinds)]
    where
    badBinds = bindsTypeValid bs
letsTypeValid' _ e@(App e' e'') = letsTypeValid' (Just e) e' ++ letsTypeValid' (Just e) e''
letsTypeValid' m e = (evalContainedASTs (letsTypeValid' m)) $ children e


-- | caseTypeValid
-- In all case expressions, the types of the Expr and Id, should match, and
-- they should also correspond to either the DataCon or Lit in the AltMatches.
-- caseTypeValid :: m -> Bool
-- caseTypeValid = evalASTs caseTypeValid'
--
-- caseTypeValid' :: Expr -> Bool
-- caseTypeValid' c@(Case e i alts) =  foldr ((&&) . (typeMatch i)) (typeMatch i e) (map typeOf alts)
-- caseTypeValid' e = caseTypeValid $ children e

