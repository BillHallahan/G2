-- | Defines various functions for verifying the types in an AST

{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.ASTVerify (letsTypeValid
                                        , caseTypeValid
                                        , castTypeValid
                                        , checkVarBinds
                                        , checkExprEnvTyping
                                        , checkAppTyping
                                        , checkPathCond
                                        , checkAssumeAssert) where
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Expr
import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Language.Typing
import G2.Internals.Language.Ids
import qualified G2.Internals.Language.PathConds as PC
import qualified G2.Internals.Language.KnownValues as KV

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

-- | altMatchType
-- Grabs out an approximate 'type' for an alternative match of a case statement,
-- even if one doesn't technically exist.
altMatchType :: AltMatch -> Type
altMatchType am = case am of
        (DataAlt con _) -> typeOf con
        (LitAlt lit) -> typeOf lit
        Default -> TyBottom

-- | pathCondExpr
-- Returns either an empty list or a list with an expr of a PathCond
pathCondExpr :: PathCond -> Expr
pathCondExpr (ExtCond e _ )   = e
pathCondExpr (AltCond _ e _) = e
pathCondExpr (ConsCond _ e _) = e
pathCondExpr (PCExists i) = Var i

-- | caseTypeValid
-- In all case expressions, the types of the Expr and Id, should match, and
-- they should also correspond to either the DataCon or Lit in the AltMatches.
caseTypeValid :: (ASTContainer m Expr) => m -> [(Id, Either Expr Alt)]
caseTypeValid = evalASTs caseTypeValid'

caseTypeValid' :: Expr -> [(Id, Either Expr Alt)]
caseTypeValid' (Case e i alts) = concat [[ (i, Left e) | not $ typeMatch i e ] , altMisMatches]
  where
    -- Filter alts by AltMatch not matching the Id of the case, then pair with Id
    nonMatchingAlts = filter (\(Alt am _) -> (not $ typeMatch (altMatchType am) i)) alts
    altMisMatches = map (\a -> (i,(Right a))) nonMatchingAlts
caseTypeValid' _ = []

-- | castTypeValid
-- In a Cast the type of the expression and the LHS of the Coercion should match. Returns
-- the list of Casts which fail to meet this specification
castTypeValid :: (ASTContainer m Expr) => m -> [Expr]
castTypeValid = evalASTs castTypeValid'

castTypeValid' :: Expr -> [Expr]
castTypeValid' c@(Cast e (lhs :~ _))
   | not $ (typeMatch lhs e) = [c]
   | otherwise = []
castTypeValid' _ = []

-- | checkVarBinds
-- All variables must be bound when used.  Variables may be bound locally,
-- by a Lam, Let, or Case expression (in the alts or the Id). Or, they may
-- be bound globally, either in the ExprEnv or as a symbolic variable.
-- Returns list of any unbound Vars
checkVarBinds :: State t -> [Id]
checkVarBinds State {expr_env = eenv,
                        curr_expr = cexpr,
                        symbolic_ids = ssids,
                        input_ids = iids} =
   evalContainedASTs (checkVarBinds' eenv (ssids ++ iids)) cexpr

checkVarBinds' :: E.ExprEnv -> [Id] -> Expr -> [Id]
checkVarBinds' eenv bound (Let b e) = checkVarBinds' eenv ((map fst b) ++ bound) e
checkVarBinds' eenv bound (Lam b e) = checkVarBinds' eenv (b:bound) e
checkVarBinds' eenv bound (Case e i alts) = (checkVarBinds' eenv bound' e) ++ (concatMap runCheckOnAlt alts)
    where
    bound' = i:bound
    runCheckOnAlt = (\(Alt am expr) -> checkVarBinds' eenv ((varIdsInAltMatch am) ++ bound') expr)
checkVarBinds' eenv bound (Var i) | not $ (E.member (idName i) eenv || i `elem` bound) = [i]
checkVarBinds' eenv bound e = evalContainedASTs (checkVarBinds' eenv bound) $ children e

-- | checkExprEnvTyping
-- For each Var corresponding to an Expr in the ExprEnv, the type in the Var's
-- Id should be the same as the type of the expression bound in the ExprEnv.
checkExprEnvTyping :: State t -> Binds
checkExprEnvTyping State {expr_env = eenv, curr_expr = cexpr} =
   evalASTs (checkExprEnvTyping' eenv) cexpr

checkExprEnvTyping' :: ExprEnv -> Expr -> Binds
checkExprEnvTyping' eenv (Var i) | E.member (idName i) eenv =
    let expr = (E.lookup (idName i) eenv) in case expr of
        Just e | not $ typeMatch i e -> [(i, e)]
        _ -> []
checkExprEnvTyping' _ _ = []


-- | checkAppTyping
-- Check that each argument to each function call is of the correct type.
-- Returns all the Apps for which the type of the center does not match one of the arguments
checkAppTyping :: (ASTContainer m Expr) => m -> [Expr]
checkAppTyping m = filter functionMatchesArgs (functionCalls m)
    where 
    -- Applicative functor to judge whether a functions arguments match the type
    functionMatchesArgs = (\a -> and (map (not . (typeMatch (appCenter a))) (passedArgs a)))

-- | checkPathCond
-- All expression in the path_conds, non_red_path_conds, Returns the list of
-- expressions which do no match type bool
checkPathCond :: State t -> [Expr]
checkPathCond State {path_conds = pconds, non_red_path_conds = nrpconds, known_values = kv} =
    pcFailsExpr ++ nrpcFails
  where
    pcFailsExpr = map pathCondExpr pcFails
    -- extracts the expressions from the [PathCond] and typechecks
    pcFails = filter (\pc -> not $ typeMatch (tyBool kv) (pathCondExpr pc)) (PC.toList pconds)
    -- Check that each expression in the non-reduced path conditions is a bool
    nrpcFails = filter (\a -> not $ typeMatch (tyBool kv) a) nrpconds
  
-- | checkAssumeAssert
-- All Expr being assumed or asserted should be of type Bool.
checkAssumeAssert :: State t -> [Expr]
checkAssumeAssert State {curr_expr = cexpr, known_values = kv} =
  evalASTs (checkAssumeAssert' kv) cexpr

checkAssumeAssert' :: KV.KnownValues -> Expr -> [Expr]
checkAssumeAssert' kv (Assume e1 _) | not $ typeMatch (tyBool kv) e1 = [e1]
checkAssumeAssert' kv (Assert _ e1 _) | not $ typeMatch (tyBool kv) e1 = [e1]
checkAssumeAssert' _ _ = []


