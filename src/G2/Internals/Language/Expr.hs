{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Language.Expr ( unApp
                                  , mkApp
                                  , mkTrue
                                  , mkFalse
                                  , mkLamCase
                                  , replaceASTs
                                  , vars
                                  , varNames
                                  , symbVars
                                  , freeVars
                                  , exprReplace
                                  , mkStrict) where

import G2.Internals.Language.AST
import G2.Internals.Language.Naming
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import qualified Data.Map as M

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

-- | Ravels the application spine
mkApp :: [Expr] -> Expr
mkApp [] = error "mkApp: empty list"
mkApp (e:[]) = e
mkApp (e1:e2:es) = mkApp (App e1 e2 : es)

mkTrue :: Expr
mkTrue = Lit $ LitBool True

mkFalse :: Expr
mkFalse = Lit $ LitBool False

-- | mkLamCase
-- Takes a function to generate Alts from a NameGen, and the binding Id of a Case Statement
-- These Alts are put inside a case statement, which is wrapped by a Lam
mkLamCase :: (NameGen -> Id -> ([Alt], NameGen)) -> Type -> NameGen -> (Expr, NameGen)
mkLamCase f t ng =
    let        
        (l_bind_id, ng2) = freshId t ng
        l_var = Var l_bind_id

        (c_bind_id, ng3) = freshId t ng2

        (alts, ng4) = f ng3 c_bind_id

        c = Lam l_bind_id $ Case l_var c_bind_id alts
    in
    (c, ng4) 

--Replaces all instances of old with new in the AST
replaceASTs :: (Eq e, AST e) => e -> e -> e -> e
replaceASTs old new e = if e == old then new else modifyChildren (replaceASTs old new) e

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

symbVars :: (ASTContainer m Expr) => ExprEnv -> m -> [Expr]
symbVars eenv = filter (symbVars' eenv) . vars

symbVars' :: ExprEnv -> Expr -> Bool
symbVars' eenv (Var (Id n _)) = E.isSymbolic n eenv
symbVars' _ _ = False

--Returns the free (unbound by a Lambda, Let, or the Expr Env) variables of an expr
freeVars :: ASTContainer m Expr => E.ExprEnv -> m -> [Id]
freeVars eenv = evalASTsM (freeVars' eenv)

-- returns (bound variables, free variables)for use with evalASTsM
freeVars' :: E.ExprEnv -> [Id] -> Expr -> ([Id], [Id])
freeVars' _ _ (Let b _) = (map fst b, [])
freeVars' _ _ (Lam b _) = ([b], [])
freeVars' eenv bound (Var i) =
    if E.member (idName i) eenv || i `elem` bound then
        ([], [])
    else
        ([], [i])
freeVars' _ _ _ = ([], [])

-- In e, replaces all eOld with eNew
exprReplace :: ASTContainer e Expr => Expr -> Expr -> e -> e
exprReplace eOld eNew = modifyContainedASTs (exprReplace')
    where
        exprReplace' :: Expr -> Expr
        exprReplace' e =
            if e == eOld
                then modifyChildren (exprReplace eOld eNew) eNew 
                else modifyChildren (exprReplace eOld eNew) e

-- Forces the complete evaluation of an expression
mkStrict :: (ASTContainer m Expr) => Walkers -> m -> m
mkStrict w = modifyContainedASTs (mkStrict' w)

mkStrict' :: Walkers -> Expr -> Expr
mkStrict' w e =
    let
        ret = returnType e
        f = case ret of
            (TyConApp n _) -> App (Var $ w M.! n)
            _ -> id
    in
    f e
