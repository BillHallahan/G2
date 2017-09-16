module G2.Internals.Language.Expr ( freeVars
								  , exprReplace) where

import G2.Internals.Language.AST
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Syntax

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
