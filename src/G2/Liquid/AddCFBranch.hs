{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddCFBranch ( CounterfactualName
                             , addCounterfactualBranch) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

type CounterfactualName = Name

-- Enables finding abstract counterexamples, by adding counterfactual branches
-- with two states.
-- (a) One state is exactly the same as the current reduce function: we lookup
--     up the var, and set the curr expr to its definition.
-- (b) [StateB] The other branch introduces a new symbolic variable x_s,
--     with the same type of s, and sets the curr expr to
--     let x = x_s in Assert (a x'_1 ... x'_n x_s) x_s
--     appropriately binding x'_i to x_i in the expression environment
--
--     This allows us to choose any value for the return type of the function.
--     In this rule, we also return a b, oldb `mappend` [(f, [x_1, ..., x_n], x)]
--     This is essentially abstracting away the function definition, leaving
--     only the information that LH also knows (that is, the information in the
--     refinment type.)
addCounterfactualBranch :: [Name] -> LHStateM CounterfactualName
addCounterfactualBranch ns = do
    cfn <- freshSeededStringN "cf"
    mapWithKeyME (addCounterfactualBranch' cfn ns)
    return cfn

addCounterfactualBranch' :: CounterfactualName -> [Name]-> Name -> Expr -> LHStateM Expr
addCounterfactualBranch' cfn ns n =
    if n `elem` ns then insertInLamsE (\_ -> addCounterfactualBranch'' cfn) else return

addCounterfactualBranch'' :: CounterfactualName -> Expr -> LHStateM Expr
addCounterfactualBranch'' cfn
    orig_e@(Let 
        [(b, _)]
        (Assert (Just (FuncCall { funcName = fn, arguments = ars })) a _)) = do
    let t = returnType orig_e
        sg = SymGen t

    -- Create lambdas, to gobble up any ApplyFrames left on the stack
    lams <- tyBindings orig_e

    -- If the type of b is not the same as e's type, we have no assumption,
    -- so we get a new b.  Otherwise, we just keep our current b,
    -- in case it is used in the assertion
    b' <- if typeOf b == t then return b else freshIdN t

    let fc = FuncCall { funcName = fn, arguments = ars', returns = (Var b')}
        e' = lams $ Let [(b', sg)] $ Tick (NamedLoc cfn) $ Assume (Just fc) a (Var b')
        -- We add the Id's from the newly created Lambdas to the arguments list
        lamI = map Var $ leadingLamIds e'
        ars' = ars ++ lamI

    return $ NonDet [orig_e, e']
addCounterfactualBranch'' cfn e = modifyChildrenM (addCounterfactualBranch'' cfn) e

-- Creates Lambda bindings to saturate the type of the given Typed thing,
-- and a list of the bindings so they can be used elsewhere
tyBindings :: Typed t => t -> LHStateM (Expr -> Expr)
tyBindings t = do
    let at = spArgumentTypes t
    fn <- freshNamesN (length at)
    return $ tyBindings' fn at

tyBindings' :: [Name] -> [ArgType] -> Expr -> Expr
tyBindings' _ [] = id
tyBindings' ns (NamedType i:ts) = Lam TypeL i . tyBindings' ns ts
tyBindings' (n:ns) (AnonType t:ts) = Lam TermL (Id n t) . tyBindings' ns ts
tyBindings' [] _ = error "Name list exhausted in tyBindings'"
