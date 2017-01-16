module G2.Core.Evaluator where

import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map  as M

-- Values are where we may return from a program evaluation.
isVal :: State -> Bool
isVal (tv, env, Var n t, pc)   = M.lookup n env == Nothing
isVal (tv, env, Const c, pc)   = True
isVal (tv, env, Lam n e t, pc) = True
isVal (tv, env, App (Lam n e t) a, pc) = False
isVal (tv, env, App f a, pc) = isVal (tv, env, f, pc) && isVal (tv, env, a, pc)
isVal (tv, env, DCon dc, pc) = True
isVal (tv, env, Case m as t, pc) = False  -- isVal (tv, env, m, pc)
isVal (tv, env, BAD, pc) = True
isVal (tv, env, UNR, pc) = True

-- Evaluation stuff
eval :: State -> [State]

-- Variables
eval (tv, env, Var n t, pc) = case M.lookup n env of
    Nothing -> [(tv, env, Var n t, pc)]
    Just ex -> [(tv, env, ex, pc)]

-- Constants
eval (tv, env, Const c, pc) = [(tv, env, Const c, pc)]

-- Lambdas
eval (tv, env, Lam n e t, pc) = [(tv, env, Lam n e t, pc)]

-- Applications
eval (tv, env, App (Lam n e1 t) e2, pc) = [(tv, env', e1', pc)]
  where ns   = M.keys env
        n'   = fresh n (ns ++ freeVars e1 (n:ns))
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env

eval (tv, env, App (Case m as t) ex, pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\((dc, pars), ae) -> ((dc, pars), App ae ex)) as
        t'  = let ((dc, pars), ae') = head as' in typeOf ae'

eval (tv, env, App ex (Case m as t), pc) = [(tv, env, Case m as' t', pc)]
  where as' = map (\((dc, pars), ae) -> ((dc, pars), App ex ae)) as
        t'  = let ((dc, pars), ae') = head as' in typeOf ae'

eval (tv, env, App f a, pc) = if isVal (tv, env, f, pc)
    then let a_ress = eval (tv, env, a, pc)
         in [(tv', env', App f a', pc') | (tv', env', a', pc') <- a_ress]
    else let f_ress = eval (tv, env, f, pc)
         in [(tv', env', App f' a, pc') | (tv', env', f', pc') <- f_ress]

-- Data Constructors
eval (tv, env, DCon dc, pc) = [(tv, env, DCon dc, pc)]

-- Case
eval (tv, env, Case (Case m1 as1 t1) as2 t2, pc) = [(tv,env,Case m1 as' t2,pc)]
  where as' = map (\((dc, pars), ae) -> ((dc, pars), Case ae as2 t2)) as1

eval (tv, env, Case m as t, pc) = if isVal (tv, env, m, pc)
    then let (d:args) = unapp m
        in case d of
            Var f t -> concatMap (\((ad, pars), ae) ->
                         let ns    = M.keys env
                             pars' = freshList pars (ns++ freeVars ae (pars++ns))
                             ae'   = replaceList ae ns pars pars'
                         in [(tv, env, ae', (m, (ad, pars')):pc)]) as
            DCon md -> concatMap (\((ad, pars), ae) ->
                if length args == length pars && md == ad
                    then let ns    = M.keys env
                             pars' = freshList pars (ns++freeVars ae (pars++ns))
                             ae'   = replaceList ae ns pars pars'
                         in [(tv, M.union (M.fromList (zip pars' args)) env
                             , ae', (m, (ad, pars')):pc)]
                    else []) as
            _ -> [(tv, env, BAD, pc)]  -- Should not be in this state. Error?
    else let m_ress = eval (tv, env, m, pc)
         in [(tv', env', Case m' as t, pc') | (tv', env', m', pc') <- m_ress]

-- BAD
eval (tv, env, BAD, pc) = [(tv, env, BAD, pc)]

-- UNR
eval (tv, env, UNR, pc) = [(tv, env, UNR, pc)]

----

-- Type determination. We need types for some SMT stuff.
typeOf :: Expr -> Type
typeOf (Var n t) = t
typeOf (Const (CInt i))  = TyInt
typeOf (Const (CReal r)) = TyReal
typeOf (Const (CChar c)) = TyChar
typeOf (Const (COp n t)) = t
typeOf (Lam n e t) = t
typeOf (App f a)   = case typeOf f of
                         TyFun l r -> r
                         t         -> TyApp t (typeOf a)
typeOf (DCon (n,i,t,a)) = let a' = reverse (a ++ [t])
                          in foldl (\a r -> TyFun r a) (head a') (tail a')
typeOf (Case m as t) = t
typeOf (BAD) = TyBottom
typeOf (UNR) = TyBottom

-- Replace a single instance of a name with a new one in an Expr.
replace :: Expr -> [Name] -> Name -> Name -> Expr
replace (Var n t) env old new     = if n == old then Var new t else Var n t
replace (Const c) env old new     = Const c
replace (Lam n e t) env old new   = let fvs  = freeVars e (n:env)
                                        bads = fvs ++ env ++ [old, new]
                                        n'   = fresh n bads
                                        e'   = replace e bads n n'
                                    in Lam n' (replace e' (n':env) old new) t
replace (App f a) env old new     = App (replace f env old new)
                                        (replace a env old new)
replace (DCon dc) env old new     = DCon dc
replace (Case m as t) env old new = Case (replace m env old new) (map r as) t
  where r ((dc, pars), ae) = let fvs   = freeVars ae (pars ++ env)
                                 bads  = fvs ++ env ++ [old, new]
                                 pars' = freshList pars bads
                                 ae'   = replaceList ae bads pars pars'
                             in ((dc, pars'), replace ae' (pars'++env) old new)
replace (BAD) env old new         = BAD
replace (UNR) env old new         = UNR

-- Replace a whole list of names with new ones in an Expr via folding.
replaceList :: Expr -> [Name] -> [Name] -> [Name] -> Expr
replaceList exp env olds news = foldl (\e (n, n') -> replace e env n n')
                                      exp $ zip olds news

-- Generates a fresh name given an old name and a list of INVALID names
fresh :: Name -> [Name] -> Name
fresh o ns = foldl (\s c -> if s == c then s ++ "a" else s) o ns

-- Generates a list of fresh names. Ensures no conflict with original old list.
freshList :: [Name] -> [Name] -> [Name]
freshList os ns = snd $ foldl (\(bads, ress) o -> let o' = fresh o bads
                                                  in (o':bads, o':ress))
                              (ns ++ os, []) os

-- Returns free variables of an expression with respect to list of bounded vars.
freeVars :: Expr -> [Name] -> [Name]
freeVars (Var n t) bvs     = if n `elem` bvs then [] else [n]
freeVars (Const c) bvs     = []
freeVars (Lam n e t) bvs   = freeVars e (n:bvs)
freeVars (App f a) bvs     = L.nub (freeVars f bvs ++ freeVars a bvs)
freeVars (DCon dc) bvs     = []
freeVars (Case m as t) bvs = L.nub (freeVars m bvs ++ as_fvs)
    where a_fv ((dc, pars), ae) = freeVars ae (pars ++ bvs)
          as_fvs = L.nub (concatMap a_fv as)
freeVars (BAD) bvs = []
freeVars (UNR) bvs = []

-- Other auxilliary and preparation functions.
unapp :: Expr -> [Expr]
unapp (App f a) = unapp f ++ [a]
unapp otherwise = [otherwise]

unlam :: Expr -> ([(Name, Type)], Expr)
unlam (Lam a e t) = let (p, e')   = unlam e
                        TyFun l r = t
                    in ((a, l):p, e')
unlam otherwise   = ([], otherwise)

initState :: TEnv -> EEnv -> Name -> State
initState t_env e_env entry = case match of
    Nothing -> error "No matching entry point. Check spelling?"
    Just ex -> let (args, exp) = unlam ex
                   pairs       = map (\a -> (fst a, Var (fst a) (snd a))) args
                   e_env'      = M.union (M.fromList pairs) e_env
               in (t_env, e_env', exp, [])
  where match = M.lookup entry e_env

runN :: [State] -> Int -> ([State], Int)
runN states 0 = (states, 0)
runN [] n     = ([], n - 1)
runN (s:ss) n = runN (ss ++ eval s) (n - 1)

