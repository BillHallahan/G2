{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.AddCFBranch ( CounterfactualName
                             , addCounterfactualBranch
                             , onlyCounterfactual
                             , elimNonTop

                             , instFuncTickName
                             , existentialInstId ) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad
import G2.Liquid.Config
import G2.Liquid.Types
import G2.Liquid.TyVarBags

import qualified Data.HashSet as S
import Data.List

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
addCounterfactualBranch :: CFModules
                        -> [Name] -- ^ Which functions to consider abstracting
                        -> LHStateM CounterfactualName
addCounterfactualBranch cf_mod ns = do
    let ns' = case cf_mod of
                CFAll -> ns
                CFOnly mods -> filter (\(Name n m _ _) -> (n, m) `S.member` mods) ns

    bag_func_ns <- return . concat =<< mapM argumentNames ns'
    inst_func_ns <- return . concat =<< mapM returnNames ns'

    createBagAndInstFuncs bag_func_ns inst_func_ns

    cfn <- freshSeededStringN "cf"
    mapWithKeyME (addCounterfactualBranch' cfn ns')
    return cfn

addCounterfactualBranch' :: CounterfactualName -> [Name] -> Name -> Expr -> LHStateM Expr
addCounterfactualBranch' cfn ns n =
    if n `elem` ns then insertInLamsE (\_ -> addCounterfactualBranch'' cfn) else return

addCounterfactualBranch'' :: CounterfactualName -> Expr -> LHStateM Expr
addCounterfactualBranch'' cfn
    orig_e@(Let 
            [(b, _)]
            (Assert (Just (FuncCall { funcName = fn, arguments = ars, returns = r })) a _)) = do
        sg <- cfRetValue ars rt

        -- If the type of b is not the same as e's type, we have no assumption,
        -- so we get a new b.  Otherwise, we just keep our current b,
        -- in case it is used in the assertion
        b' <- if typeOf b == rt then return b else freshIdN rt

        let fc = FuncCall { funcName = fn, arguments = ars, returns = (Var b')}
            e' = Let [(b', sg)] $ Tick (NamedLoc cfn) $ Assume (Just fc) a (Var b')

        return $ NonDet [orig_e, e']
        where
            rt = typeOf r
addCounterfactualBranch'' cfn e = modifyChildrenM (addCounterfactualBranch'' cfn) e

cfRetValue :: [Expr] -- ^ Arguments
           -> Type -- ^ Type of return value
           -> LHStateM Expr
cfRetValue ars rt
    | tvs <- tyVarIds rt
    , not (null tvs)  = do
        let all_tvs = tvs ++ tyVarIds ars
        ty_bags <- getTyVarBags

        ex_vrs <- freshIdsN (map TyVar all_tvs)
        let ex_tvs_to_vrs = zip all_tvs ex_vrs

        ex_ty_clls <- mapM 
                        (\tv -> wrapExtractCalls
                              . filter nullNonDet
                              . concat
                              =<< mapM (extractTyVarCall ty_bags ex_tvs_to_vrs tv) ars) (nub all_tvs)

        let ex_let_bnds = zip ex_vrs ex_ty_clls

        dUnit <- mkUnitE

        insts_f <- getInstFuncs
        inst_ret <- instTyVarCall insts_f ex_tvs_to_vrs rt
        let inst_ret_call = App inst_ret dUnit
        ir_bndr <- freshIdN (typeOf inst_ret_call)
        
        return . Let ((ir_bndr, inst_ret_call):ex_let_bnds) $ Tick (NamedLoc instFuncTickName) (Var ir_bndr)
    | otherwise = do 
        return (SymGen SNoLog rt)

nullNonDet :: Expr -> Bool
nullNonDet (NonDet []) = False
nullNonDet _ = True

instFuncTickName :: Name
instFuncTickName = Name "INST_FUNC_TICK" Nothing 0 Nothing

argumentNames :: ExState s m => Name -> m [Name]
argumentNames n = do
    e <- lookupE n
    case e of
        Just e' -> return . concatMap tyConNames $ anonArgumentTypes e'
        Nothing -> return []

returnNames :: ExState s m => Name -> m [Name]
returnNames n = do
    e <- lookupE n
    case e of
        Just e' -> return . tyConNames $ returnType e'
        Nothing -> return []

tyConNames :: Type -> [Name]
tyConNames (TyCon n t) = n:tyConNames t 
tyConNames t = evalChildren tyConNames t

-- | Eliminates the real branch of the non-deterministic choices, leaving only
-- the abstract branch.  Assumes all non-determinisitic choices are for
-- counterfactual symbolic execution.
onlyCounterfactual :: ASTContainer m Expr => m -> m
onlyCounterfactual = modifyASTs onlyCounterfactual'

onlyCounterfactual' :: Expr -> Expr
onlyCounterfactual' (NonDet [_, e]) = e
onlyCounterfactual' e = e

-- | Eliminate all Asserts, except for the functions with names in the HashSet
elimNonTop :: S.HashSet Name -> State t -> State t
elimNonTop hs s@(State { expr_env = eenv }) = s { expr_env = E.mapWithKey (elimNonTop' hs) eenv }

elimNonTop' :: S.HashSet Name -> Name -> Expr -> Expr
elimNonTop' hs n e = if n `S.member` hs then e else elimAsserts e
