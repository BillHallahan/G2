module G2.Core.Evaluator where

import G2.Core.Language
import G2.Core.Models

import qualified Data.Map as M

-- Values of evaluation:
-- v = c [p]
--   | Lam x e
--   | DataCon [p]
--   | x [p]
--   | case (x [p]) of ...

isValue :: State -> Bool
isValue (env, Const c, pc) = True
isValue (env, Lam x e, pc) = True
isValue (env, DCon dc, pc) = True
isValue (env, Var n, pc) = M.lookup n env == Nothing
isValue (env, App fe ae, pc) = isValue (env, fe, pc) && isValue (env, ae, pc)
isValue (env, Case m as, pc) = isValue (env, m, pc)

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
  where n'   = fresh n $ M.keys env
        e1'  = replace n n' e1
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
    then concatMap (\((dc, par), ae) ->
        let (d:args) = unrollApp m
        in if length args == length par && d == DCon dc
            then let ns  = M.keys env
                     (ns',par') = foldl (\(cs,r) p -> let p' = fresh p cs
                                          in (p':cs,p':r)) (ns,[]) par
                     ae' = foldl (\e (n,n') -> replace n n' e) ae $ zip par par'
                 in [(M.union (M.fromList (zip par' args)) env
                     , ae', (m,(dc,par')):pc)]
            else []) as
    else let m_ress = eval (env, m, pc)
         in [(env', Case m' as, pc') | (env', m', pc') <- m_ress]

----

fresh :: Name -> [Name] -> Name
fresh n ns = foldl (\s c -> if s == c then s ++ "a" else s) n ns

replace :: Name -> Name -> Expr -> Expr
replace old new exp = case exp of
    Var a     -> if a == old then Var new else Var a
    Const c   -> Const c
    Lam n lex -> if n == old then Lam n lex else Lam n (replace old new lex) 
    App fe ae -> App (replace old new fe) (replace old new ae)
    DCon dc   -> DCon dc
    Case m as -> let r ((d,ar),e) = if old `elem` ar
                                        then ((d, ar), e)
                                        else ((d, ar), replace old new e)
                 in Case m (map r as)
    
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

