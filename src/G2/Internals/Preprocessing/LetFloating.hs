module G2.Internals.Preprocessing.LetFloating (letFloat) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

import Data.Foldable
import Data.List
import Data.Monoid hiding (Alt)

-- We lift all let bindings to functions into the expr env.
-- This is needed to allow for defunctionalization, as if a function is in a let
-- clause, rather than the expr env, it cannot be called by the apply function

letFloat :: State -> State
letFloat s@State { expr_env = eenv
                 , name_gen = ng} =
            let
                (eenv', ng') = letFloat' eenv ng
            in
            s { expr_env = eenv'
              , name_gen = ng' }

letFloat' :: E.ExprEnv -> NameGen -> (E.ExprEnv, NameGen)
letFloat' eenv ng =
    let
        hasLet = filter (hasHigherOrderLetBinds) . E.toExprList $ E.filterWithKey (\n _ -> E.isRoot n eenv) eenv
    in
    letFloat'' hasLet eenv ng

letFloat'' :: [(Name, Expr)] -> E.ExprEnv -> NameGen -> (E.ExprEnv, NameGen)
letFloat'' [] eenv ng = (eenv, ng)
letFloat'' ((n,e):ne) eenv ng =
    let
        (e', eenv', ng') = liftLetBinds eenv ng e

        eenv'' = E.insert n e' eenv'
    in
    letFloat'' ne eenv'' ng'

liftLetBinds :: E.ExprEnv -> NameGen -> Expr -> (Expr, E.ExprEnv, NameGen)
liftLetBinds eenv ng (Let b e) =
    let
        (funcs, notFuncs) = partition (hasFuncType . fst) b
        (e', eenv', ng') = liftLetBinds' eenv ng funcs e

        (e'', eenv'', ng'') = liftLetBinds eenv' ng' e'
    in
    (Let notFuncs e'', eenv'', ng'')
liftLetBinds eenv ng (App e1 e2) =
    let
        (e1', eenv', ng') = liftLetBinds eenv ng e1
        (e2', eenv'', ng'') = liftLetBinds eenv' ng' e2
    in
    (App e1' e2', eenv'', ng'')
liftLetBinds eenv ng (Lam i e) =
    let
        (e', eenv', ng') = liftLetBinds eenv ng e
    in
    (Lam i e', eenv', ng')
liftLetBinds eenv ng (Case e i a) =
    let
        (e', eenv', ng') = liftLetBinds eenv ng e
        (a', eenv'', ng'') = liftLetBindsAlts eenv' ng' a
    in
    (Case e' i a', eenv'', ng'')
liftLetBinds eenv ng (Assume e1 e2) =
    let
        (e1', eenv', ng') = liftLetBinds eenv ng e1
        (e2', eenv'', ng'') = liftLetBinds eenv' ng' e2
    in
    (Assume e1' e2', eenv'', ng'')
liftLetBinds eenv ng (Assert e1 e2) =
    let
        (e1', eenv', ng') = liftLetBinds eenv ng e1
        (e2', eenv'', ng'') = liftLetBinds eenv' ng' e2
    in
    (Assert e1' e2', eenv'', ng'')
liftLetBinds eenv ng e = (e, eenv, ng)

liftLetBindsAlts :: E.ExprEnv -> NameGen -> [Alt] -> ([Alt], E.ExprEnv, NameGen)
liftLetBindsAlts eenv ng [] = ([], eenv, ng)
liftLetBindsAlts eenv ng (Alt am e:as) =
    let
        (e', eenv', ng') = liftLetBinds eenv ng e
        (a', eenv'', ng'') = liftLetBindsAlts eenv' ng' as
    in
    (Alt am e':a', eenv'', ng'')

liftLetBinds' :: E.ExprEnv -> NameGen -> Binds -> Expr -> (Expr, E.ExprEnv, NameGen)
liftLetBinds' eenv ng [] e = (e, eenv, ng)
liftLetBinds' eenv ng ((Id n t, b):xs) e =
    let
        --Lift to ExprEnv
        (n', ng') = freshSeededName n ng
        (b', fv, ng'') = freeVarsToLams eenv ng' n b
        b'' = rename n n' b'
        eenv' = E.insert n' b'' eenv

        --Replace Vars in function
        newCall = foldr App (Var (Id n' t)) (map Var fv)
        e' = replaceAST (Var (Id n t)) newCall e
    in
    liftLetBinds' eenv' ng'' xs e'

-- Adjusts the free variables of am expression to have new, lambda bound names
-- Returns this new expression, a list of the old ids in the order of their corresponding
-- lambdas, and a new namgen
freeVarsToLams :: E.ExprEnv -> NameGen -> Name -> Expr -> (Expr, [Id], NameGen)
freeVarsToLams eenv ng n e =
    let
        fv = filter (\i' -> idName i' /= n) $ freeVars eenv e
        fvN = map idName fv
        fvT = map typeOf fv

        (fr, ng') = freshSeededNames fvN ng 
        
        frId = map (uncurry Id) (zip fr fvT)

        e' = foldr (uncurry rename) e (zip fvN fr)
        e'' = foldr (Lam) e' frId
    in
    (e'', fv, ng')    

--Replaces all instances of old with new in the AST
replaceAST :: (Eq e, AST e) => e -> e -> e -> e
replaceAST old new e = if e == old then new else modifyChildren (replaceAST old new) e

hasHigherOrderLetBinds :: (ASTContainer m Expr) => m -> Bool
hasHigherOrderLetBinds = getAny . evalASTs hasHigherOrderLetBinds'

hasHigherOrderLetBinds' :: Expr -> Any
hasHigherOrderLetBinds' (Let b _) = Any $ any (hasFuncType . fst) b
hasHigherOrderLetBinds' _ = Any False