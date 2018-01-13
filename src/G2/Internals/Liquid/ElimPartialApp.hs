module G2.Internals.Liquid.ElimPartialApp (elimPartialApp) where

-- We eliminate partial function definitions, so that we can access all
-- variables in the annotations

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

import Data.Foldable
import Data.Tuple

elimPartialApp :: State -> State
elimPartialApp s@(State {expr_env = eenv, name_gen = ng }) =
    let
        mr = maximum $ E.map' req eenv

        (ns, ng') = freshNames mr ng

        eenv' = modifyContainedASTs (elimPartialApp' ns) eenv
    in
    s { expr_env = eenv', name_gen = ng' }

req :: Expr -> Int
req e =
    let
        lc = lamsCount e
        ra = numArgs e
    in    
    ra - lc

elimPartialApp' :: [Name] -> Expr -> Expr
elimPartialApp' ns e =
    let        
        diff = req e

        ad = map (\n -> Id n TyBottom) $ take diff ns

        e' = insertInLams (\_ _e -> foldr Lam _e ad) e
    in
    insertInLams (\_ _e -> foldl' App _e $ map Var ad) e'

addLam :: Id -> Expr -> Expr
addLam i e = Lam i $ App e (Var i)

lamsCount :: Expr -> Int
lamsCount (Lam _ e) = 1 + lamsCount e
lamsCount _ = 0