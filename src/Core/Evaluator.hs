module G2.Core.Evaluator where

import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map  as M

-- Values are where we may return from a program evaluation.
isVal :: State -> Bool
isVal (env, Var n t, pc)   = M.lookup n env == Nothing
isVal (env, Const c t, pc) = True
isVal (env, Lam n e t, pc) = True
isVal (env, App (Lam n e t) a, pc) = False
isVal (env, App f a, pc)   = isVal (env, f, pc) && isVal (env, a, pc)
isVal (env, DCon dc, pc)   = True
isVal (env, Case m as t, pc) = isVal (env, m, pc)
isVal (env, BAD, pc) = True
isVal (env, UNR, pc) = True

-- Evaluation stuff
eval :: State -> [State]

-- Variables
eval (env, Var n t, pc) = case M.lookup n env of
    Nothing -> [(env, Var n t, pc)]
    Just ex -> [(env, ex, pc)]

-- Constants
eval (env, Const c t, pc) = [(env, Const c t, pc)]

-- Lambdas
eval (env, Lam n e t, pc) = [(env, Lam n e t, pc)]

-- Applications
eval (env, App (Lam n e1 t) e2, pc) = [(env', e1', pc)]
  where ns   = M.keys env
        n'   = fresh n (ns ++ freeVars e1 (n:ns))
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env

eval (env, App (Case m as t) ex, pc) = [(env, Case m as' t', pc)]
  where as' = map (\((dc, pars), ae) -> ((dc, pars), App ae ex)) as
        t'  = let ((dc, pars), ae) = head as' in typeOf ae


eval (env, App f a, pc) = if isVal (env, f, pc)
    then let a_ress = eval (env, a, pc)
         in [(env', App f a', pc') | (env', a', pc') <- a_ress]
    else let f_ress = eval (env, f, pc)
         in [(env', App f' a, pc') | (env', f', pc') <- f_ress]

-- Data Constructors
eval (env, DCon dc, pc) = [(env, DCon dc, pc)]

-- Case
eval (env, Case (Case m1 as1 t1) as2 t2, pc) = [(env, Case m1 as' t2, pc)]
  where as' = map (\((dc, par), ae) -> ((dc, par), Case ae as2 t2)) as1

eval (env, Case m as t, pc) = if isVal (env, m, pc)
    then let (d:args) = unrollApp m
        in case d of
            Var f t -> concatMap (\((ad, par), ae) ->
                         let ns   = M.keys env
                             par' = freshList par (ns ++ freeVars ae (par++ns))
                             ae'  = replaceList ae ns par par'
                         in [(env, ae', (m, (ad, par')):pc)]) as
            DCon md -> concatMap (\((ad, par), ae) ->
                if length args == length par && md == ad
                    then let ns   = M.keys env
                             par' = freshList par (ns ++ freeVars ae (par++ns))
                             ae'  = replaceList ae ns par par'
                         in [(M.union (M.fromList (zip par' args)) env
                             , ae', (m, (ad, par')):pc)]
                    else []) as
            _ -> [(env, BAD, pc)]  -- Should not be in this state. Throw error?
    else let m_ress = eval (env, m, pc)
         in [(env', Case m' as t, pc') | (env', m', pc') <- m_ress]

-- BAD
eval (env, BAD, pc) = [(env, BAD, pc)]

-- UNR
eval (env, UNR, pc) = [(env, UNR, pc)]

----

-- Type determination. We need types for some SMT stuff.
typeOf :: Expr -> Type
typeOf (Var n t)   = t
typeOf (Const c t) = t
typeOf (Lam n e t) = t
typeOf (App f a)   = case typeOf f of
                         TyFun l r -> r
typeOf (DCon (n,i,t,a)) = let a' = reverse (a ++ [t])
                          in foldl (\a r -> TyFun r a) (head a') (tail a')
typeOf (Case m as t) = t
typeOf (BAD) = TyBottom
typeOf (UNR) = TyBottom


-- Replace a single instance of a name with a new one in an Expr.
replace :: Expr -> [Name] -> Name -> Name -> Expr
replace (Var n t) env old new     = if n == old then Var new t else Var n t
replace (Const c t) env old new   = (Const c t)
replace (Lam n e t) env old new   = let fvs  = freeVars e (n:env)
                                        bads = fvs ++ env ++ [old, new]
                                        n'   = fresh n bads
                                        e'   = replace e bads n n'
                                    in Lam n' (replace e' (n':env) old new) t
replace (App f a) env old new     = App (replace f env old new)
                                        (replace a env old new)
replace (DCon dc) env old new     = (DCon dc)
replace (Case m as t) env old new = Case (replace m env old new) (map r as) t
  where r ((dc, par), ae) = let fvs  = freeVars ae (par ++ env)
                                bads = fvs ++ env ++ [old, new]
                                par' = freshList par bads
                                ae'  = replaceList ae bads par par'
                            in ((dc, par'), replace ae' (par' ++ env) old new)
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
freeVars (Const c t) bvs   = []
freeVars (Lam n e t) bvs   = freeVars e (n:bvs)
freeVars (App f a) bvs     = L.nub (freeVars f bvs ++ freeVars a bvs)
freeVars (DCon dc) bvs     = []
freeVars (Case m as t) bvs = L.nub (freeVars m bvs ++ as_fvs)
    where a_fv ((dc, par), ae) = freeVars ae (par ++ bvs)
          as_fvs = L.nub (concatMap a_fv as)
freeVars (BAD) bvs = []
freeVars (UNR) bvs = []

-- Other auxilliary and preparation functions.
unrollApp :: Expr -> [Expr]
unrollApp (App f a) = unrollApp f ++ [a]
unrollApp otherwise = [otherwise]

unlam :: Expr -> ([(Name, Type)], Expr)
unlam (Lam a e t) = let (p, e')   = unlam e
                        TyFun l r = t
                    in ((a, l):p, e')
unlam otherwise   = ([], otherwise)

initState :: Env -> Name -> State
initState env entry = case match of
    Nothing -> error "No matching entry point. Check spelling?"
    Just ex -> let (args, exp) = unlam ex
                   pairs       = map (\a -> (fst a, Var (fst a) (snd a))) args
                   env'        = M.union (M.fromList pairs) env
               in (env', exp, [])
  where match = M.lookup entry env

