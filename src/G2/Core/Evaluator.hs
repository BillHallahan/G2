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
isVal State {eEnv = env, cExpr = Var n _} = M.lookup n env == Nothing
isVal State {cExpr = App (Lam _ _ _) _} = False
isVal State {cExpr = App (Case _ _ _) _} = False
isVal s@State {cExpr = App f a} = isVal (s {cExpr = f}) && isVal (s {cExpr = a})
isVal State {cExpr = Case _ _ _} = False  -- isVal (tv, env, m, pc)
isVal _ = True

{- Evaluation

The evaluation function takes a state and returns potentially more states if
it runs into branching statements.
-}
evaluate :: State -> [State]

{- Var

We treat unbound variables as symbolic values during execution.
-}
evaluate s@State{cExpr = Var n t} = case M.lookup n (eEnv s) of
    Nothing -> [s]
    Just ex -> [s {cExpr = ex}]

-- Const
evaluate s@State{cExpr = Const c} = [s]


-- Lambda
evaluate s@State{cExpr = Lam n e t} = [s]

{- App -- Special case of lambda application.

If we apply to a Lambda, we must make sure that we do not get naming conflicts
within the body of the lambda function before we bind the argument to the
environment.

Note: Our environment grows larger during execution. Probably not a problem.
-}
evaluate s@State{eEnv = env, cExpr = App (Lam n e1 t) e2, slt = slt} = [s {eEnv = env', cExpr = e1', slt = slt'}]
  where ns   = M.keys env
        n'   = fresh n (ns ++ freeVars (n:ns) e1)
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env
        slt' = updateSymLinkTableList [n'] [n] slt

{- App -- Special case of application on the right of a case.

Apply commuting conversions to shove the RHS of the App inside the case.
-}
evaluate s@State {cExpr = App (Case m as t) ex} = [s {cExpr = Case m as' t'}]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ae ex)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'

{- App -- Special case of application on the left of a case.

Apply commuting conversions to shove the LHS of the App inside the case.
-}
evaluate s@State {cExpr = App ex (Case m as t)} = [s {cExpr = Case m as' t'}]
  where as' = map (\(Alt (dc, pars), ae) -> (Alt (dc, pars), App ex ae)) as
        t'  = let (Alt (dc, pars), ae') = head as' in typeOf ae'


{- App

To preserve lazy evaluation semantics we want to evalute the LHS of the App
as much as possible before performing evaluation on the RHS.
-}
evaluate s@State{cExpr = App f a} = if isVal (s {cExpr = f})
    then let a_ress = evaluate (s {cExpr = a})
         in [s' {tEnv = tv', eEnv = ev', cExpr = App f a'} | s'@State {tEnv = tv', eEnv = ev', cExpr = a'} <- a_ress]
    else let f_ress = evaluate (s {cExpr = f})
         in [s' {tEnv = tv', eEnv = ev', cExpr = App f' a} | s'@State {tEnv = tv', eEnv = ev', cExpr = f'} <- f_ress]
-- evaluate (tv, env, App f a, pc) = if isVal (tv, env, f, pc)
--     then let a_ress = evaluate (tv, env, a, pc)
--          in [(tv', env', App f a', pc') | (tv', env', a', pc') <- a_ress]
--     else let f_ress = evaluate (tv, env, f, pc)
--          in [(tv', env', App f' a, pc') | (tv', env', f', pc') <- f_ress]

-- Data Constructors
evaluate s@State{cExpr =  DCon dc} = [s]

{- Case -- Special case of nested case statements

In nested case statements, we apply more commuting conversions to shove it.
-}
evaluate s@State{cExpr = Case (Case m1 as1 t1) as2 t2} = [s{cExpr = Case m1 as' t2}]
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

evaluate s@State {cExpr = Case m as t} = if isVal (s {cExpr = m})
    then let non_defaults = filter (not . isDefault) as
             defaults     = filter isDefault as -- Handle differently
         in (do_nd (s {cExpr = Case m non_defaults t}) ++
            (do_d (s {cExpr = Case m defaults t}) non_defaults))
    else let m_ress = evaluate s {cExpr = m}
         in [s' {cExpr = Case m' as t} | s'@State {cExpr = m'} <- m_ress]
  where -- This is behavior we expect to match from the G2 Prelude's default.
        isDefault :: (Alt, Expr) -> Bool
        isDefault (Alt (DC ("DEFAULT", 0, TyBottom, []), _), _) = True
        isDefault _ = False

        do_nd :: State -> [State]
        do_nd s@State {eEnv = env, cExpr = Case m nds t, pc = pc', slt = slt} =
          let (d:args) = unapp m
          in case d of
            Var f t -> concatMap (\(Alt (ad, pars), ae) ->
             let ns    = M.keys env
                 pars' = freshList pars (ns ++ names s)--(ns++freeVars (pars++ns) ae)
                 ae'   = replaceList ae ns pars pars'
                 slt'  = updateSymLinkTableList pars' pars slt
             in [s {cExpr = ae', pc = (m, Alt (ad, pars'), True):pc', slt = slt'}]) nds
            DCon md -> concatMap (\(Alt (ad, pars), ae) ->
              if length args == length pars && md == ad
                  then let ns = M.keys env
                           pars' = freshList pars (ns ++ names s)--(ns ++ freeVars (pars++ns) ae)
                           ae'   = replaceList ae ns pars pars'
                           slt'  = updateSymLinkTableList pars' pars slt
                       in [s {eEnv = M.union (M.fromList (zip pars' args)) env
                           , cExpr = ae', pc = (m, Alt (ad, pars'), True):pc', slt = slt'}]
                  else []) nds
            _ -> [s {cExpr = BAD}]  -- Should not be in this state. Error?

        -- We are technically only supposed to have at most a single DEFAULT
        -- appear in any given pattern matching. If this is not the case, then
        -- Core Haskell did something wrong and it's not our problem.
        do_d :: State -> [(Alt, Expr)] -> [State]
        do_d s@State {cExpr = Case m ds t, pc = pc'} nds =
          let (d:args) = unapp m
              neg_alts = map fst nds
              neg_pcs  = map (\na -> (m, na, False)) neg_alts
          in map (\(Alt _, ae) -> s {cExpr = ae, pc = neg_pcs ++ pc'}) ds

-- Type
evaluate s@State {cExpr = Type t} = [s]

-- BAD
evaluate s@State {cExpr = BAD} = [s]

-- UNR
evaluate s@State {cExpr = UNR} = [s]

------------------

-- Unroll the App spine.
unapp :: Expr -> [Expr]
unapp (App f a) = unapp f ++ [a]
unapp e = [e]

replaceVars :: EEnv -> Expr -> (Expr, SymLinkTable)
replaceVars e_env ex = 
    let 
        (args, expr) = unlam ex
        ns = M.keys e_env
        nfs = map fst args
        types = map snd args
        nfs' = freshList nfs (ns ++ (freeVars (ns ++ nfs) expr))
        slt = M.fromList . zip nfs' . zip3 nfs types $ map Just [1..]
     in
     (replaceList expr ns nfs nfs', slt)

lamBinding :: EEnv -> Expr -> (Expr, SymLinkTable)
lamBinding e_env ex = 
    let 
        args = leadingLams ex
        ns = M.keys e_env
        nfs = map fst args
        types = map snd args
        nfs' = freshList nfs (ns ++ (freeVars (ns ++ nfs) ex))
        nfs'' = freshList nfs (ns ++ nfs' ++ (freeVars (ns ++ nfs) ex))
        slt = M.fromList . zip nfs'' . zip3 nfs types $ map Just [1..]

        env = ns ++ nfs' ++ nfs'' ++ (freeVars (ns ++ nfs) ex)
     in
     (foldr (\(n, n', t) ex' -> App ex' (Var n' t)) ex . zip3 nfs' nfs'' $ types, slt)
     --(insertLams ex env (zip3 nfs' nfs'' types), slt)--foldl (\ex' (n, t) -> App ex' (Var n t)) ex (reverse . zip nfs' $ types)--(replaceList expr ns nfs nfs', slt)
     where
        leadingLams :: Expr -> [(Name, Type)]
        leadingLams (Lam n e (TyFun t _)) = (n, t):leadingLams e
        leadingLams _ = []

        insertLams :: Expr -> [Name] -> [(Name, Name, Type)] -> Expr
        insertLams e _ [] = e
        insertLams (Lam n e t) env ((n', n'', t'):xs) =
            let
                e' = replace e env n n'
            in
            App (Lam n' (insertLams e' env xs) t) (Var n'' t')

{- Initialization

We create our starting state by giving the initState function our type and
expression environment as well as the entrypoint function name. If our entry
point is a function with arguments (in the form of cascading lambdas), we need
to strip out all the parameters and ensure that they are now free variables
within the body of the first non-immediately cascading lambda expression.

initStateWithPost is similar, but allows passing in a post condition
-}
initState :: TEnv -> EEnv -> Name -> State
initState t_env e_env entry =
    case match of
        Nothing -> error "No matching entry point. Check spelling?"
        Just ex -> let (expr', slt) = replaceVars e_env ex
                   in State t_env e_env expr' [] slt M.empty
    where match = M.lookup entry e_env

initStateWithPost :: TEnv -> EEnv -> Name -> Name -> State
initStateWithPost t_env e_env post entry =
    case match of
        (Just post_ex, Just ex) -> let
                        post_type = typeOf post_ex
                        --(expr', slt) = replaceVars e_env ex
                        (expr', slt) = lamBinding e_env ex
                   in State t_env e_env (App (Var post post_type) expr') [] slt M.empty
        otherwise -> error "No matching entry points. Check spelling?"
    where match = (M.lookup post e_env, M.lookup entry e_env)

-- Count the number of times we call eval as a way of limiting runs.
runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN states n = runN (concatMap (\s -> evaluate s) states) (n - 1)

-- runN :: [State] -> Int -> ([State], Int)
-- runN states 0 = (states, 0)
-- runN [] n     = ([], n - 1)
-- runN (s:ss) n = runN (ss ++ evaluate s) (n - 1)

-- Attempt to count the number of function applications, and use them to limit runs... not working currently
stackN :: State -> Int -> [State]
stackN s 0 = [s]
stackN s@State {cExpr = cExpr'} i
    | leadVar cExpr' = concatMap (\s' -> stackN s' (i - 1)) (evaluate s)
    | otherwise = 
        let
            evS = evaluate s
            (evSF, evSC) = L.partition (exprEqUpToName (cExpr s) . cExpr) evS
        in
        evSF ++ (concatMap (\s' -> stackN s' i) evSC)
    where
        leadVar :: Expr -> Bool
        leadVar (App e _) = leadVar e
        leadVar (Var _ _) = True
        leadVar _ = False
