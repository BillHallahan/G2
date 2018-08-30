{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Language.Expr ( module G2.Internals.Language.Casts
                                  , replaceVar
                                  , unApp
                                  , mkApp
                                  , mkDCTrue
                                  , mkDCFalse
                                  , mkTrue
                                  , mkFalse
                                  , mkBool
                                  , mkDCInt
                                  , mkDCInteger
                                  , mkDCFloat
                                  , mkDCDouble
                                  , mkCons
                                  , mkEmpty
                                  , mkIdentity
                                  , modifyAppLHS
                                  , modifyAppRHS
                                  , modifyInLHS
                                  , functionCalls
                                  , nonDataFunctionCalls
                                  , appCenter
                                  , mapArgs
                                  , mkLams
                                  -- , mkLamBindings
                                  -- , mkMappedLamBindings
                                  , leadingLamUsesIds
                                  , leadingLamIds
                                  , insertInLams
                                  , maybeInsertInLams
                                  , inLams
                                  , replaceASTs
                                  , args
                                  , passedArgs
                                  , nthArg
                                  , vars
                                  , varIds
                                  , varNames
                                  , varId
                                  , symbVars
                                  , freeVars
                                  , alphaReduction
                                  , varBetaReduction
                                  , mkStrict) where

import G2.Internals.Language.AST
import G2.Internals.Language.Casts
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import Data.Foldable
import qualified Data.Map as M
import Data.Maybe
import Data.Semigroup

import Debug.Trace

replaceVar :: (ASTContainer m Expr) => Name -> Expr -> m -> m
replaceVar n re = modifyASTs (replaceVar' n re)

replaceVar' :: Name -> Expr -> Expr -> Expr
replaceVar' n re v@(Var (Id n' _)) = if n == n' then re else v
replaceVar' _ _ e = e

-- | unApp
-- Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

-- | mkApp
-- Turns the Expr list into an application spine
mkApp :: [Expr] -> Expr
mkApp [] = error "mkApp: empty list"
mkApp (e:[]) = e
mkApp (e1:e2:es) = mkApp (App e1 e2 : es)

mkDCInt :: KnownValues -> TypeEnv -> Expr
mkDCInt kv tenv = Data . fromJust $ getDataCon tenv (KV.tyInt kv) (KV.dcInt kv)

mkDCInteger :: KnownValues -> TypeEnv -> Expr
mkDCInteger kv tenv = Data . fromJust $ getDataCon tenv (KV.tyInteger kv) (KV.dcInteger kv)

mkDCFloat :: KnownValues -> TypeEnv -> Expr
mkDCFloat kv tenv = Data . fromJust $ getDataCon tenv (KV.tyFloat kv) (KV.dcFloat kv)

mkDCDouble :: KnownValues -> TypeEnv -> Expr
mkDCDouble kv tenv = Data . fromJust $ getDataCon tenv (KV.tyDouble kv) (KV.dcDouble kv)

mkDCTrue :: KnownValues -> TypeEnv -> DataCon
mkDCTrue kv tenv = fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)

mkDCFalse :: KnownValues -> TypeEnv -> DataCon
mkDCFalse kv tenv = fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcFalse kv)

mkTrue :: KnownValues -> TypeEnv -> Expr
mkTrue kv tenv = Data . fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)

mkFalse :: KnownValues -> TypeEnv -> Expr
mkFalse kv tenv = Data . fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcFalse kv)

mkBool :: KnownValues -> TypeEnv -> Bool -> Expr
mkBool kv tenv b = if b then mkTrue kv tenv else mkFalse kv tenv

mkCons :: KnownValues -> TypeEnv -> Expr
mkCons kv tenv = Data . fromJust $ getDataCon tenv (KV.tyList kv) (KV.dcCons kv)

mkEmpty :: KnownValues -> TypeEnv -> Expr
mkEmpty kv tenv = Data . fromJust $ getDataCon tenv (KV.tyList kv) (KV.dcEmpty kv)

mkIdentity :: Type -> Expr
mkIdentity t =
    let
        x = Id (Name "x" Nothing 0 Nothing) t
    in
    Lam TermL x (Var x)

-- | modifyAppLHS
modifyAppLHS :: (Expr -> Expr) -> Expr -> Expr
modifyAppLHS f (App e e') = App (f e) (modifyAppLHS f e')
modifyAppLHS _ e = e

-- | modifyAppRHS
modifyAppRHS :: (Expr -> Expr) -> Expr -> Expr
modifyAppRHS f (App e e') = App (modifyAppRHS f e) (f e')
modifyAppRHS _ e = e

modifyInLHS :: (Expr -> Expr) -> Expr -> Expr
modifyInLHS f (App e _) = modifyInLHS f e
modifyInLHS f e = f e

-- | functionCalls
-- Returns all function calls with all arguments
functionCalls :: ASTContainer m Expr => m -> [Expr]
functionCalls = evalContainedASTs functionCalls'

functionCalls' :: Expr -> [Expr]
functionCalls' e@(App e' e'') = e:functionCallsApp e' ++ functionCalls' e''
functionCalls' e = functionCalls $ children e

functionCallsApp :: Expr -> [Expr]
functionCallsApp (App e e') = functionCallsApp e ++ functionCalls' e'
functionCallsApp _ = []

-- | nonDataFunctionCalls
-- Returns all function calls to Vars with all arguments
nonDataFunctionCalls :: ASTContainer m Expr => m -> [Expr]
nonDataFunctionCalls = filter (not . centerIsData) . functionCalls

centerIsData :: Expr -> Bool
centerIsData (App e _) = centerIsData e
centerIsData (Data _) = True
centerIsData _ = False

appCenter :: Expr -> Expr
appCenter (App a _) = appCenter a
appCenter e = e

mapArgs :: (Expr -> Expr) -> Expr -> Expr
mapArgs f (App e e') = App (mapArgs f e) (f e')
mapArgs _ e = e

mkLams :: [(LamUse, Id)] ->  Expr -> Expr
mkLams =  flip (foldr (\(u, i) -> Lam u i))

-- Generates a lambda binding for each a in the provided list
-- Takes a function to generate the inner expression
-- mkLamBindings :: NameGen -> [Type] -> (NameGen -> [Id] -> (Expr, NameGen)) -> (Expr, NameGen)
-- mkLamBindings ng ts f =
--     let
--         (is, ng') = freshIds ts ng

--         (e, ng'') = f ng' is
--     in
--     (foldr Lam is e, ng'')

-- mkMappedLamBindings :: NameGen -> [(a, Type)] -> (NameGen -> [(a, Id)] -> (Expr, NameGen)) -> (Expr, NameGen)
-- mkMappedLamBindings ng at f =
--     let
--         (as, _) = unzip at
--     in
--     mkLamBindings ng (map snd at) (\ng' ns -> f ng' (zip as ns))

-- Runs the given function f on the expression nested in the lambdas, and
-- rewraps the new expression with the Lambdas
insertInLams :: ([Id] -> Expr -> Expr) -> Expr -> Expr
insertInLams f = insertInLams' f []

insertInLams' :: ([Id] -> Expr -> Expr) -> [Id] -> Expr -> Expr
insertInLams' f xs (Lam u i e)  = Lam u i $ insertInLams' f (i:xs) e
insertInLams' f xs e = f (reverse xs) e

maybeInsertInLams :: ([Id] -> Expr -> Maybe Expr) -> Expr -> Maybe Expr
maybeInsertInLams f = maybeInsertInLams' f []

maybeInsertInLams' :: ([Id] -> Expr -> Maybe Expr) -> [Id] -> Expr -> Maybe Expr
maybeInsertInLams' f xs (Lam u i e)  = fmap (Lam u i) $ maybeInsertInLams' f (i:xs) e
maybeInsertInLams' f xs e = f (reverse xs) e

-- | inLams
-- Returns the Expr in nested Lams
inLams :: Expr -> Expr
inLams (Lam _ _ e) = inLams e
inLams e = e

leadingLamUsesIds :: Expr -> [(LamUse, Id)]
leadingLamUsesIds (Lam u i e) = (u, i):leadingLamUsesIds e
leadingLamUsesIds _ = []

leadingLamIds :: Expr -> [Id]
leadingLamIds (Lam _ i e) = i:leadingLamIds e
leadingLamIds _ = []

args :: Expr -> [Id]
args (Lam _ i e) = i:args e
args _ = []

passedArgs :: Expr -> [Expr]
passedArgs (App e e') = e':passedArgs e
passedArgs _ = []

nthArg :: Expr -> Int -> Id
nthArg e i = args e !! (i - 1)


--Returns all Vars in an ASTContainer
vars :: (ASTContainer m Expr) => m -> [Expr]
vars = evalASTs vars'

vars' :: Expr -> [Expr]
vars' v@(Var _) = [v]
vars' _ = []

varId :: Expr -> Maybe Id
varId (Var i) = Just i
varId _ = Nothing

symbVars :: (ASTContainer m Expr) => ExprEnv -> m -> [Expr]
symbVars eenv = filter (symbVars' eenv) . vars

symbVars' :: ExprEnv -> Expr -> Bool
symbVars' eenv (Var (Id n _)) = E.isSymbolic n eenv
symbVars' _ _ = False

-- | freeVars
-- Returns the free (unbound by a Lambda, Let, or the Expr Env) variables of an expr
freeVars :: ASTContainer m Expr => E.ExprEnv -> m -> [Id]
freeVars eenv = evalASTsM (freeVars' eenv)

freeVars' :: E.ExprEnv -> [Id] -> Expr -> ([Id], [Id])
freeVars' _ _ (Let b _) = (map fst b, [])
freeVars' _ _ (Lam _ b _) = ([b], [])
freeVars' eenv bound (Var i) =
    if E.member (idName i) eenv || i `elem` bound then
        ([], [])
    else
        ([], [i])
freeVars' _ _ _ = ([], [])

alphaReduction :: ASTContainer m Expr => m -> m
alphaReduction = modifyASTsM alphaReduction'

alphaReduction' :: Max Int -> Expr -> (Expr, Max Int)
alphaReduction' mi l@(Lam u i@(Id (Name n m ii lo) t) e) =
    let
        mi' = mi + 1
        n' = Name n m (getMax mi') lo
        i' = Id n' t

        e' = replaceASTs (Var i) (Var i') e
    in
    if ii > getMax mi then (l, mi') else (Lam u i' e', mi')
alphaReduction' m e = (e, m)

-- | varBetaReduction
-- Performs beta reduction, if a Var is being applied 
varBetaReduction :: ASTContainer m Expr => m -> m
varBetaReduction = modifyASTs varBetaReduction'

varBetaReduction' :: Expr -> Expr
varBetaReduction' a@(App (Lam _ i e) (Var v)) = 
    if not (isTYPE . typeOf $ i) then replaceLamIds i v e else a
varBetaReduction' e = e

replaceLamIds :: Id -> Id -> Expr -> Expr
replaceLamIds i i' v@(Var v') = if i == v' then Var i' else v
replaceLamIds i i' l@(Lam u l' e) = if i == l' then l else Lam u l' (replaceLamIds i i' e)
replaceLamIds i i' e = modifyChildren (replaceLamIds i i') e

-- | mkStrict
-- Forces the complete evaluation of an expression
mkStrict :: (ASTContainer m Expr) => Walkers -> m -> m
mkStrict w = modifyContainedASTs (mkStrict' w)

mkStrict' :: Walkers -> Expr -> Expr
mkStrict' w e =
    let
        rt = returnType e
        t = tyAppCenter rt
        ts = tyAppArgs rt
    in
    case t of
        (TyConApp n _) -> case M.lookup n w of
            Just i -> App (foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)) e
            Nothing -> error $ "mkStrict: failed to find walker with type: " ++ show n
        _ -> error $ "No walker found in mkStrict\n e = " ++ show e ++ "\nt = " ++ show (typeOf e) ++ "\nret = " ++ show (returnType e)

typeToWalker :: Walkers -> Type -> Expr
typeToWalker w t
  | TyConApp n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
  case M.lookup n w of
    Just i -> foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)
    Nothing -> error $ "typeToWalker: failed to find type: " ++ show n
typeToWalker _ t = mkIdentity t
