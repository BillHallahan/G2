module G2.Core.Evaluator where

import G2.Core.CoreManipulator
import G2.Core.Language
import G2.Core.Utils

import qualified Data.List as L
import qualified Data.Map  as M

{- Values

We need to return values from evaluation and this is it. Only oddity may be
that we are able to return lambda expressions during evaluation.
-}
isVal :: State -> Bool
isVal (tv, env, Var n t, pc)   = M.lookup n env == Nothing
isVal (tv, env, Const c, pc)   = True
isVal (tv, env, Lam n e t, pc) = True
isVal (tv, env, App (Lam n e t) a, pc) = False
isVal (tv, env, App f a, pc) = isVal (tv, env, f, pc) && isVal (tv, env, a, pc)
isVal (tv, env, DCon dc, pc) = True
isVal (tv, env, Case m as t, pc) = False  -- isVal (tv, env, m, pc)
isVal (tv, env, Type t, pc) = True
isVal (tv, env, BAD, pc) = True
isVal (tv, env, UNR, pc) = True

{- Evaluation

The evaluation function takes a state and returns potentially more states if
it runs into branching statements.
-}
eval :: State -> [State]

{- Var

We treat unbound variables as symbolic values during execution.
-}
eval (tv, env, Var n t, pc) = case M.lookup n env of
    Nothing -> [(tv, env, Var n t, pc)]
    Just ex -> [(tv, env, ex, pc)]

-- Const
eval (tv, env, Const c, pc) = [(tv, env, Const c, pc)]


-- Lambda
eval (tv, env, Lam n e t, pc) = [(tv, env, Lam n e t, pc)]

{- App -- Special case of lambda application.

If we apply to a Lambda, we must make sure that we do not get naming conflicts
within the body of the lambda function before we bind the argument to the
environment.

Note: Our environment grows larger during execution. Probably not a problem.
-}
eval (tv, env, App (Lam n e1 t) e2, pc) = [(tv, env', e1', pc)]
  where ns   = M.keys env
        n'   = fresh n (ns ++ freeVars (n:ns) e1)
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env

{- App -- Special case of application on the right of a case.
  
Apply commuting conversions to shove the RHS of the App inside the case.
-}
eval (tv, env, App (Case m as t) ex, pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ae ex)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'

{- App -- Special case of application on the left of a case.

Apply commuting conversions to shove the LHS of the App inside the case.
-}
eval (tv, env, App ex (Case m as t), pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ex ae)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'


{- App

To preserve lazy evaluation semantics we want to evalute the LHS of the App
as much as possible before performing evaluation on the RHS.
-}
eval (tv, env, App f a, pc) = if isVal (tv, env, f, pc)
    then let a_ress = eval (tv, env, a, pc)
         in [(tv', env', App f a', pc') | (tv', env', a', pc') <- a_ress]
    else let f_ress = eval (tv, env, f, pc)
         in [(tv', env', App f' a, pc') | (tv', env', f', pc') <- f_ress]

-- Data Constructors
eval (tv, env, DCon dc, pc) = [(tv, env, DCon dc, pc)]

{- Case -- Special case of nested case statements

In nested case statements, we apply more commuting conversions to shove it.
-}
eval (tv, env, Case (Case m1 as1 t1) as2 t2, pc) = [(tv,env,Case m1 as' t2,pc)]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), Case ae as2 t2)) as1

{- Case

Consider the expression:

    case A b c of
        K1 b c   -> ...
        K2 b c d -> ...

There are two possible things that A may be:

1. A is a data constructor: We just continue along the branch that it can
   performs a match on. Note that we need to, as usual, bind the variables to
   the arguments, and make sure there are fresh names.

2. A is an unbound variable: Thus A must be a function that can return an ADT
   to match one of the data constructors (might be unsat though), and hence
   we must match it to every single data constructor that we come along.
   Furthermore, because A's return result may be completely arbitrary, it does
   not make sense for the parameters of some data constructor that it matches
   to have bindings to an expression. Rather, they also continue on as unbound
   free variables that would also more or less be symbolics.
-}
eval (tv, env, Case m as t, pc) = if isVal (tv, env, m, pc)
    then let (d:args) = unapp m
        in case d of
            Var f t -> concatMap (\(Alt (ad, pars), ae) ->
                         let ns    = M.keys env
                             pars' = freshList pars (ns++freeVars (pars++ns) ae)
                             ae'   = replaceList ae ns pars pars'
                         in [(tv, env, ae', (m, Alt (ad, pars')):pc)]) as
            DCon md -> concatMap (\(Alt (ad, pars), ae) ->
                if length args == length pars && md == ad
                    then let ns    = M.keys env
                             pars' = freshList pars (ns++freeVars (pars++ns) ae)
                             ae'   = replaceList ae ns pars pars'
                         in [(tv, M.union (M.fromList (zip pars' args)) env
                             , ae', (m, Alt (ad, pars')):pc)]
                    else []) as
            _ -> [(tv, env, BAD, pc)]  -- Should not be in this state. Error?
    else let m_ress = eval (tv, env, m, pc)
         in [(tv', env', Case m' as t, pc') | (tv', env', m', pc') <- m_ress]

-- Type
eval (tv, env, Type t, pc) = [(tv, env, Type t, pc)]

-- BAD
eval (tv, env, BAD, pc) = [(tv, env, BAD, pc)]

-- UNR
eval (tv, env, UNR, pc) = [(tv, env, UNR, pc)]

------------------

-- Replace a single instance of a name with a new one in an Expr.
replace :: Expr -> [Name] -> Name -> Name -> Expr
replace (Var n t) env old new     = if n == old then Var new t else Var n t
replace (Const c) env old new     = Const c
replace (Lam n e t) env old new   = let fvs  = freeVars (n:env) e
                                        bads = fvs ++ env ++ [old, new]
                                        n'   = fresh n bads
                                        e'   = replace e bads n n'
                                    in Lam n' (replace e' (n':env) old new) t
replace (App f a) env old new     = App (replace f env old new)
                                        (replace a env old new)
replace (DCon dc) env old new     = DCon dc
replace (Case m as t) env old new = Case (replace m env old new) (map r as) t
  where r :: (Alt, Expr) -> (Alt, Expr)
        r (Alt (dc, pars), ae) =
            let
                fvs = freeVars (pars ++ env) ae
                bads  = fvs ++ env ++ [old, new]
                pars' = freshList pars bads
                ae' = replaceList ae bads pars pars'
            in
            (Alt (dc, pars'), replace ae' (pars'++env) old new)
replace (Type t) env old new = Type t
replace BAD env old new = BAD
replace UNR env old new = UNR

-- Replace a whole list of names with new ones in an Expr via folding.
replaceList :: Expr -> [Name] -> [Name] -> [Name] -> Expr
replaceList expr env olds news = foldl (\e (n, n') -> replace e env n n')
                                      expr $ zip olds news

-- Generates a fresh name given an old name and a list of INVALID names
fresh :: Name -> [Name] -> Name
fresh o ns = foldl (\s c -> if s == c then s ++ [head c] else s) o ns

-- Generates a list of fresh names. Ensures no conflict with original old list.
freshList :: [Name] -> [Name] -> [Name]
freshList os ns = snd $ foldl (\(bads, ress) o -> let o' = fresh o bads
                                                  in (o':bads, ress++[o']))
                              (ns ++ os, []) os

-- Returns free variables of an expression with respect to list of bounded vars.
freeVars :: [Name] -> Expr -> [Name]
freeVars bv e = snd 
                . evalExpr' (freeVars')
                    (\(bv1, fv1) (bv2, fv2) -> (L.nub (bv1 ++ bv2), L.nub (fv1 ++ fv2)))
                    e $ (bv, [])
    where
        freeVars' :: ([Name], [Name]) -> Expr -> ([Name], [Name])
        freeVars' (bv, fr) (Var n' _) = if n' `elem` bv then ([], []) else ([], [n'])
        freeVars' (bv, fr) (Lam n' _ _) = ([n'], [])
        freeVars' _ _ = ([], [])

-- Returns free variables of an expression with respect to list of bounded vars.
-- freeVars :: Expr -> [Name] -> [Name]
-- freeVars (Var n t) bvs     = if n `elem` bvs then [] else [n]
-- freeVars (Const c) bvs     = []
-- freeVars (Lam n e t) bvs   = freeVars e (n:bvs)
-- freeVars (App f a) bvs     = L.nub (freeVars f bvs ++ freeVars a bvs)
-- freeVars (DCon dc) bvs     = []
-- freeVars (Case m as t) bvs = L.nub (freeVars m bvs ++ as_fvs)
--     where a_fv :: (Alt, Expr) -> [Name]
--           a_fv ((dc, pars), ae) = freeVars ae (pars ++ bvs)
--           as_fvs = L.nub (concatMap a_fv as)
-- freeVars (Type t) bvs = []
-- freeVars BAD bvs = []
-- freeVars UNR bvs = []

-- Unroll the App spine.
unapp :: Expr -> [Expr]
unapp (App f a) = unapp f ++ [a]
unapp otherwise = [otherwise]

-- Unroll cascading lambda expressions.
unlam :: Expr -> ([(Name, Type)], Expr)
unlam (Lam a e t) = let (p, e')   = unlam e
                        TyFun l r = t
                    in ((a, l):p, e')
unlam otherwise   = ([], otherwise)

{- Initialization

We create our starting state by giving the initState function our type and
expression environment as well as the entrypoint function name. If our entry
point is a function with arguments (in the form of cascading lambdas), we need
to strip out all the parameters and ensure that they are now free variables
within the body of the first non-immediately cascading lambda expression.
-}
initState :: TEnv -> EEnv -> Name -> State
initState t_env e_env entry = case match of
    Nothing -> error "No matching entry point. Check spelling?"
    Just ex -> let (args, expr) = unlam ex
                   ns          = M.keys e_env
                   nfs         = map fst args
                   nfs'        = freshList nfs (ns++(freeVars (ns ++ nfs) expr))
                   expr'       = replaceList expr ns nfs nfs'
               in (t_env, e_env, expr', [])
  where match = M.lookup entry e_env

-- Count the number of times we call eval as a way of limiting runs.
runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN (s:ss) n = runN (ss ++ eval s) (n - 1)

