module G2.Core.Evaluator where

import G2.Core.Language
import G2.Core.Utils

import qualified Data.List as L
import qualified Data.Map as M

{- Values

We need to return values from evaluation and this is it. Only oddity may be
that we are able to return lambda expressions during evaluation.
-}
isVal :: State -> Bool
isVal (_, env, Var n _, _) = M.lookup n env == Nothing
isVal (_, _, App (Lam _ _ _) _, _) = False
isVal (tv, env, App f a, pc) = isVal (tv, env, f, pc) && isVal (tv, env, a, pc)
isVal (_, _, Case _ _ _, _) = False  -- isVal (tv, env, m, pc)
isVal _ = True

{- Evaluation

The evaluation function takes a state and returns potentially more states if
it runs into branching statements.
-}
evaluate :: State -> [State]

{- Var

We treat unbound variables as symbolic values during execution.
-}
evaluate (tv, env, Var n t, pc) = case M.lookup n env of
    Nothing -> [(tv, env, Var n t, pc)]
    Just ex -> [(tv, env, ex, pc)]

-- Const
evaluate (tv, env, Const c, pc) = [(tv, env, Const c, pc)]


-- Lambda
evaluate (tv, env, Lam n e t, pc) = [(tv, env, Lam n e t, pc)]

{- App -- Special case of lambda application.

If we apply to a Lambda, we must make sure that we do not get naming conflicts
within the body of the lambda function before we bind the argument to the
environment.

Note: Our environment grows larger during execution. Probably not a problem.
-}
evaluate (tv, env, App (Lam n e1 t) e2, pc) = [(tv, env', e1', pc)]
  where ns   = M.keys env
        n'   = fresh n (ns ++ freeVars (n:ns) e1)
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env

{- App -- Special case of application on the right of a case.

Apply commuting conversions to shove the RHS of the App inside the case.
-}
evaluate (tv, env, App (Case m as t) ex, pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ae ex)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'

{- App -- Special case of application on the left of a case.

Apply commuting conversions to shove the LHS of the App inside the case.
-}
evaluate (tv, env, App ex (Case m as t), pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ex ae)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'


{- App

To preserve lazy evaluation semantics we want to evalute the LHS of the App
as much as possible before performing evaluation on the RHS.
-}
evaluate (tv, env, App f a, pc) = if isVal (tv, env, f, pc)
    then let a_ress = evaluate (tv, env, a, pc)
         in [(tv', env', App f a', pc') | (tv', env', a', pc') <- a_ress]
    else let f_ress = evaluate (tv, env, f, pc)
         in [(tv', env', App f' a, pc') | (tv', env', f', pc') <- f_ress]

-- Data Constructors
evaluate (tv, env, DCon dc, pc) = [(tv, env, DCon dc, pc)]

{- Case -- Special case of nested case statements

In nested case statements, we apply more commuting conversions to shove it.
-}
evaluate (tv, env, Case (Case m1 as1 t1) as2 t2, pc) = [(tv,env,Case m1 as' t2,pc)]
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

evaluate (tv, env, Case m as t, pc) = if isVal (tv, env, m, pc)
    then let non_defaults = filter (not . isDefault) as
             defaults     = filter isDefault as -- Handle differently
         in (do_nd (tv, env, Case m non_defaults t, pc)) ++
            (do_d (tv, env, Case m defaults t, pc) non_defaults)
    else let m_ress = evaluate (tv, env, m, pc)
         in [(tv', env', Case m' as t, pc') | (tv', env', m', pc') <- m_ress]
  where -- This is behavior we expect to match from the G2 Prelude's default.
        isDefault :: (Alt, Expr) -> Bool
        isDefault (Alt (DC ("DEFAULT", 0, TyBottom, []), _), _) = True
        isDefault _ = False

        do_nd :: State -> [State]
        do_nd (tv, env, Case m nds t, pc) =
          let (d:args) = unapp m
          in case d of
            Var f t -> concatMap (\(Alt (ad, pars), ae) ->
             let ns    = M.keys env
                 pars' = freshList pars (ns++freeVars (pars++ns) ae)
                 ae'   = replaceList ae ns pars pars'
             in [(tv, env, ae', (m, Alt (ad, pars'), True):pc)]) nds
            DCon md -> concatMap (\(Alt (ad, pars), ae) ->
              if length args == length pars && md == ad
                  then let ns    = M.keys env
                           pars' = freshList pars (ns++freeVars (pars++ns) ae)
                           ae'   = replaceList ae ns pars pars'
                       in [(tv, M.union (M.fromList (zip pars' args)) env
                           , ae', (m, Alt (ad, pars'), True):pc)]
                  else []) nds
            _ -> [(tv, env, BAD, pc)]  -- Should not be in this state. Error?

        -- We are technically only supposed to have at most a single DEFAULT
        -- appear in any given pattern matching. If this is not the case, then
        -- Core Haskell did something wrong and it's not our problem.
        do_d :: State -> [(Alt, Expr)] -> [State]
        do_d (tv, env, Case m ds t, pc) nds =
          let (d:args) = unapp m
              neg_alts = map fst nds
              neg_pcs  = map (\na -> (m, na, False)) neg_alts
          in map (\(Alt _, ae) -> (tv, env, ae, neg_pcs ++ pc)) ds

-- Type
evaluate (tv, env, Type t, pc) = [(tv, env, Type t, pc)]

-- BAD
evaluate (tv, env, BAD, pc) = [(tv, env, BAD, pc)]

-- UNR
evaluate (tv, env, UNR, pc) = [(tv, env, UNR, pc)]

------------------

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
                   nfs'        = freshList nfs (ns ++ (freeVars (ns ++ nfs) expr))
                   expr'       = replaceList expr ns nfs nfs'
               in (t_env, e_env, expr', [])
  where match = M.lookup entry e_env

-- Count the number of times we call eval as a way of limiting runs.
runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN (s:ss) n = runN (ss ++ evaluate s) (n - 1)

