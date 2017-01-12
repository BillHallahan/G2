module G2.Core.Evaluator where

import G2.Core.Language
import G2.Core.Models

import qualified Data.List as L
import qualified Data.Map  as M

-- Values of evaluation:
-- v = c [p]
--   | Lam x e
--   | DataCon [p]
--   | x [p]
--   | case (x [p]) of ...

isValue :: State -> Bool
isValue (env, Var n, pc) = M.lookup n env == Nothing
isValue (env, Const c, pc) = True
isValue (env, Lam x e, pc) = True
isValue (env, DCon dc, pc) = True
isValue (env, App (Lam n fe) ae, pc) = False
isValue (env, App fe ae, pc) = isValue (env, fe, pc) && isValue (env, ae, pc)
isValue (env, Case m as, pc) = isValue (env, m, pc)
isValue (env, BAD, pc) = True
isValue (env, UNR, pc) = True

eval :: State -> [State]

-- Variables
eval (env, Var n, pc) = case M.lookup n env of
    Nothing -> [(env, Var n, pc)]
    Just ex -> [(env, ex, pc)]

-- Constants
eval (env, Const c, pc) = [(env, Const c, pc)]

-- Lambdas
eval (env, Lam n exp, pc) = [(env, Lam n exp, pc)]

-- Applications
eval (env, App (Lam n e1) e2, pc) = [(env', e1', pc)]
  where ns   = M.keys env
        n'   = fresh n ns
        e1'  = replace e1 ns n n'
        env' = M.insert n' e2 env

eval (env, App (Case m as) e2, pc) = [(env, Case m as', pc)]
  where as' = map (\((dc, args), cexp) -> ((dc, args), App cexp e2)) as

eval (env, App fe ae, pc) = if isValue (env, fe, pc)
    then let a_ress = eval (env, ae, pc)
         in [(env', App fe ae', pc') | (env', ae', pc') <- a_ress]
    else let f_ress = eval (env, fe, pc)
         in [(env', App fe' ae, pc') | (env', fe', pc') <- f_ress]

-- Data Constructors
eval (env, DCon dc, pc) = [(env, DCon dc, pc)]

-- Case
eval (env, Case (Case m1 as1) as2, pc) = [(env, Case m1 as', pc)]
  where as' = map (\((dc, ns), exp) -> ((dc, ns), Case exp as2)) as1

eval (env, Case m as, pc) = if isValue (env, m, pc)
    then let (d:args) = unrollApp m
         in case d of
            Var f   -> undefined
            DCon md -> concatMap (\((ad, par), ae) ->
                if length args == length par && ad == md
                    then let ns   = M.keys env
                             par' = freshList par ns
                             ae'  = replaceList ae ns par par'
                         in [(M.union (M.fromList (zip par' args)) env
                             , ae', (m,(ad,par')):pc)]
                    else []) as
            _ -> [(env, BAD, pc)] -- Should not be in this state.
    else let m_ress = eval (env, m, pc)
         in [(env', Case m' as, pc') | (env', m', pc') <- m_ress]

-- BAD
eval (env, BAD, pc) = [(env, BAD, pc)]

-- UNR
eval (env, UNR, pc) = [(env, UNR, pc)]

----

-- Generates a fresh name given an old name and a list of invalid names.
fresh :: Name -> [Name] -> Name
fresh o ns = foldl (\s c -> if s == c then s ++ "a" else s) o ns

-- Generates a list of fresh names. Ensures new list does not conflict with old.
freshList :: [Name] -> [Name] -> [Name]
freshList os ns = snd $ foldl (\(cs, rs) o -> let o' = fresh o cs
                                              in (o':cs, o':rs))
                              (ns ++ os, []) os

-- Replace a single instance of a name with a new one in an Expr.
replace :: Expr -> [Name] -> Name -> Name -> Expr
replace (Var n) env old new     = if n == old then Var new else Var n
replace (Lam n e) env old new   = let fv = freeVars e (n:env)
                                      cf = fv ++ env ++ [old, new] -- conflicts
                                      n' = fresh n cf
                                      e' = replace e cf n n'
                                  in Lam n' (replace e' (n':env) old new)
replace (App f a) env old new   = App (replace f env old new)
                                      (replace a env old new)
replace (Case m as) env old new = Case (replace m env old new) (map r as)
    where r ((d,ar),e) = let fv = freeVars e (ar ++ env)
                             cf = fv ++ env ++ [old, new]
                             ns = freshList ar cf
                             e' = replaceList e cf ar ns
                         in ((d, ns), replace e' (ns ++ env) old new) 
replace otherwise env old new   = otherwise

-- Replace a whole list of names with new ones in an Expr via folding.
replaceList :: Expr -> [Name] -> [Name] -> [Name] -> Expr
replaceList exp env olds news = foldl (\e (n, n') -> replace e env n n')
                                      exp $ zip olds news

-- Returns the free variables of an expression with respect to bounded vars.
freeVars :: Expr -> [Name] -> [Name]
freeVars (Var n) bvs   = if n `elem` bvs then [] else [n]
freeVars (Const c) bvs = []
freeVars (Lam n e) bvs = freeVars e (n:bvs)
freeVars (App f a) bvs = L.nub (freeVars f bvs ++ freeVars a bvs)
freeVars otherwise bvs = []

unrollApp :: Expr -> [Expr]
unrollApp (App f a) = unrollApp f ++ [a]
unrollApp otherwise = [otherwise]

unlam :: Expr -> ([Name], Expr)
unlam (Lam a e) = let (p, e') = unlam e in (a:p, e')
unlam otherwise = ([], otherwise)

initState :: EEnv -> Name -> State
initState env entry = case match of
    Nothing -> error "no matching entry point. Check spelling?"
    Just ex -> let (args, exp) = unlam ex
                   pairs       = zip args $ map Var args
                   env'        = M.union (M.fromList pairs) env
               in (env', exp, [])
  where match = M.lookup entry env

