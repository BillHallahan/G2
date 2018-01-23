{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Expr ( module G2.Internals.Language.Casts
                                  , replaceVar
                                  , unApp
                                  , mkApp
                                  , mkTrue
                                  , mkFalse
                                  , mkBool
                                  , mkDCInt
                                  , mkDCDouble
                                  , mkIdentity
                                  , functionCalls
                                  , nonDataFunctionCalls
                                  , mkLamBindings
                                  , mkMappedLamBindings
                                  , leadingLamIds
                                  , insertInLams
                                  , replaceASTs
                                  , args
                                  , passedArgs
                                  , nthArg
                                  , vars
                                  , varNames
                                  , varId
                                  , symbVars
                                  , freeVars
                                  , mkStrict) where

import G2.Internals.Language.AST
import G2.Internals.Language.Casts
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv
import G2.Internals.Language.Typing

import Data.Foldable
import qualified Data.Map as M
import Data.Maybe

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

mkDCFloat :: KnownValues -> TypeEnv -> Expr
mkDCFloat kv tenv = Data . fromJust $ getDataCon tenv (KV.tyFloat kv) (KV.dcFloat kv)

mkDCDouble :: KnownValues -> TypeEnv -> Expr
mkDCDouble kv tenv = Data . fromJust $ getDataCon tenv (KV.tyDouble kv) (KV.dcDouble kv)


mkTrue :: KnownValues -> TypeEnv -> Expr
mkTrue kv tenv = Data . fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)

mkFalse :: KnownValues -> TypeEnv -> Expr
mkFalse kv tenv = Data . fromJust $ getDataCon tenv (KV.tyBool kv) (KV.dcFalse kv)

mkBool :: KnownValues -> TypeEnv -> Bool -> Expr
mkBool kv tenv b = if b then mkTrue kv tenv else mkFalse kv tenv

mkIdentity :: Type -> Expr
mkIdentity t =
    let
        x = Id (Name "x" Nothing 0) t
    in
    Lam x (Var x)

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

-- Generates a lambda binding for each a in the provided list
-- Takes a function to generate the inner expression
mkLamBindings :: NameGen -> [Type] -> (NameGen -> [Id] -> (Expr, NameGen)) -> (Expr, NameGen)
mkLamBindings ng ts f =
    let
        (is, ng') = freshIds ts ng

        (e, ng'') = f ng' is
    in
    (foldr Lam e is, ng'')

mkMappedLamBindings :: NameGen -> [(a, Type)] -> (NameGen -> [(a, Id)] -> (Expr, NameGen)) -> (Expr, NameGen)
mkMappedLamBindings ng at f =
    let
        (as, _) = unzip at
    in
    mkLamBindings ng (map snd at) (\ng ns -> f ng (zip as ns))

-- Runs the given function f on the expression nested in the lambdas, and
-- rewraps the new expression with the Lambdas
insertInLams :: ([Id] -> Expr -> Expr) -> Expr -> Expr
insertInLams f = insertInLams' f []

insertInLams' :: ([Id] -> Expr -> Expr) -> [Id] -> Expr -> Expr
insertInLams' f xs (Lam i e)  = Lam i $ insertInLams' f (i:xs) e
insertInLams' f xs e = f (reverse xs) e

leadingLamIds :: Expr -> [Id]
leadingLamIds (Lam i e) = i:leadingLamIds e
leadingLamIds _ = []

args :: Expr -> [Id]
args (Lam i e) = i:args e
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

varNames :: (ASTContainer m Expr) => m -> [Name]
varNames = evalASTs varNames'

varNames' :: Expr -> [Name]
varNames' (Var (Id n _)) = [n]
varNames' _ = []

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
freeVars' _ _ (Lam b _) = ([b], [])
freeVars' eenv bound (Var i) =
    if E.member (idName i) eenv || i `elem` bound then
        ([], [])
    else
        ([], [i])
freeVars' _ _ _ = ([], [])

-- | mkStrict
-- Forces the complete evaluation of an expression
mkStrict :: (ASTContainer m Expr) => Walkers -> m -> m
mkStrict w = modifyContainedASTs (mkStrict' w)

mkStrict' :: Walkers -> Expr -> Expr
mkStrict' w e =
    case returnType e of
        (TyConApp n ts) -> case M.lookup n w of
            Just i -> App (foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)) e
            Nothing -> error $ "mkStrict: failed to find walker with type: " ++ show n
        _ -> error "No walker found in mkStrict'"

typeToWalker :: Walkers -> Type -> Expr
typeToWalker w (TyConApp n ts) =
  case M.lookup n w of
    Just i -> foldl' (App) (Var i) (map Type ts ++ map (typeToWalker w) ts)
    Nothing -> error $ "typeToWalker: failed to find type: " ++ show n
typeToWalker _ t = mkIdentity t
