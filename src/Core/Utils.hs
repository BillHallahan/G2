{-# LANGUAGE FlexibleContexts #-}

module G2.Core.Utils where

import G2.Core.CoreManipulator
import G2.Core.Language

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Monoid as Mon

sp2 = "  "
sp4 = sp2 ++ sp2

mkStateStr :: State -> String
mkStateStr (tv, ev, expr, pc) = L.intercalate "\n\n" li
  where li = ["> Type Env:\n" ++ ts,  "> Expr Env:\n" ++ es
             ,"> Curr Expr:\n" ++ xs, "> Path Constraints:\n" ++ ps]
        ts = mkTypeEnvStr tv
        es = mkExprEnvStr ev
        xs = mkExprStr expr
        ps = mkPCStr pc

mkStatesStr :: [State] -> String
mkStatesStr []     = ""
mkStatesStr (s:[]) = mkStateStr s
mkStatesStr (s:ss) = mkStateStr s ++ divLn ++ mkStatesStr ss
  where divLn = "\n--------------\n"

mkTypeEnvStr :: TEnv -> String
mkTypeEnvStr tenv = L.intercalate "\n" (map ntStr (M.toList tenv))
  where ntStr :: (Name, Type) -> String
        ntStr (n, t) = n ++ "\n" ++ sp4 ++ show t

mkExprEnvStr :: EEnv -> String
mkExprEnvStr eenv = L.intercalate "\n" (map neStr (M.toList eenv))
  where neStr :: (Name, Expr) -> String
        neStr (n, e) = n ++ "\n" ++ sp4 ++ mkExprStr e


mkExprStr :: Expr -> String
mkExprStr e = mkExprStr' e 0
    where
        mkExprStr' :: Expr -> Int -> String
        mkExprStr' (Var n t) i = off i ++ "Var " ++ n ++ " (" ++ mkTypeStr t (i + 1) ++")"
        mkExprStr' (Lam n e t) i = 
            let
                e' = mkExprStr' e (i + 1)
            in
            off i ++  "Lam (" ++ show n ++ "\n" ++ e' ++ " " ++ mkTypeStr t i ++")"
        mkExprStr' (App e1 e2) i = 
            let
                e1' = mkExprStr' e1 (i + 1)
                e2' = mkExprStr' e2 (i + 1)
            in
            off i ++ "App (\n" ++ e1' ++ "\n" ++ e2' ++ "\n" ++ off i ++ ")"
        mkExprStr' (Case e1 ae t) i = 
            let
                e1' = mkExprStr' e1 (i + 1)
                ae' = mkAltExprStr ae (i + 1)
            in
            off i ++ "Case (\n" ++ e1' ++ "\n" ++ ae' ++ " " ++ mkTypeStr t i ++ ")"
        mkExprStr' (Type t) i = off i ++ "Type (" ++ mkTypeStr t (i + 1) ++ ")"
        mkExprStr' x i = off i ++ show x


        mkAltExprStr :: [(Alt, Expr)] -> Int -> String
        mkAltExprStr [] i = ""
        mkAltExprStr ((a, e):xs) i = off i ++ "(" ++ show a ++ ",\n" ++ 
                                        mkExprStr' e (i + 1) ++ ")\n" ++ mkAltExprStr xs i

        off :: Int -> String
        off i = duplicate "   " i


mkTypeStr :: Type -> Int -> String
mkTypeStr t i = mkTypeStr' t i False
    where
        mkTypeStr' :: Type -> Int -> Bool -> String
        mkTypeStr' (TyFun t1 t2) i  b = tPat t1 t2 "TyFun" i b 
        mkTypeStr' (TyApp t1 t2) i  b = tPat t1 t2 "TyApp" i b 
        mkTypeStr' (TyConApp n tx) i b = 
            let li = L.intercalate ", " . map (\t' -> mkTypeStr' t' (i + 1) b) $ tx in
                off i b ++ "TyConApp " ++ show n ++ " [" ++ li ++ "]"
        mkTypeStr' (TyForAll n t) i b = off i b ++ "TyForAll " ++ show n ++
                                        "(" ++ mkTypeStr' t (i + 1) b ++ ")"
        mkTypeStr' t i b = (if b then " " else "") ++ show t

        tPat :: Type -> Type -> String -> Int -> Bool -> String
        tPat t1 t2 s i b = off i b ++ s ++ " (" 
                            ++ mkTypeStr' t1 (i + 1) True 
                            ++ mkTypeStr' t2 (i + 1) True ++ off i True ++  ")"

        off :: Int -> Bool -> String
        off i b = if b then "\n" ++ duplicate "   " i else ""


-- Primitive for now because I'm low on battery.
mkPCStr :: PC -> String
mkPCStr []     = ""
mkPCStr (p:[]) = show p
mkPCStr (p:ps) = show p ++ "\n--AND--\n" ++ mkPCStr ps

duplicate :: String -> Int -> String
duplicate s 0 = ""
duplicate s n = s ++ duplicate s (n - 1)

{- Type judgement

Really the only two cases here worth mentioning are App and DCon.

App: We must consider the possibility that the LHS is a function type, or not,
and pop off whatever we need as necessary, or wrap it in TyApp to not cause problems.

DCon: We reconstruct the function type that data constructors truly represent.
-}
typeOf :: Expr -> Type
typeOf (Var n t) = t
typeOf (Const (CInt i))    = TyRawInt
typeOf (Const (CFloat f))  = TyRawFloat
typeOf (Const (CDouble d)) = TyRawDouble
typeOf (Const (CChar c))   = TyRawChar
typeOf (Const (CString s)) = TyRawString
typeOf (Const (COp n t)) = t
typeOf (Lam n e t) = t
typeOf (App f a)   = case typeOf f of
                         TyFun l r -> r
                         t         -> TyApp t (typeOf a)
typeOf (DCon (DC (n,i,t,a))) = let a' = reverse (a ++ [t])
                          in foldl (\a r -> TyFun r a) (head a') (tail a')
typeOf (Case m as t) = t
typeOf (Type t) = t
typeOf _ = TyBottom

-- Replace a single instance of a name with a new one in an Expr.
replace :: Expr -> [Name] -> Name -> Name -> Expr
replace e env old new = modify'' (replace' old new) e env
    where
        replace' :: Name -> Name -> [Name] -> Expr -> (Expr, [Name])
        replace' old new env (Var n t) = if n == old then (Var new t, []) else (Var n t, [])
        replace' old new env (Lam n e t)  =
            let 
                fvs  = freeVars (n:env) e
                bads = fvs ++ env ++ [old, new]
                n'   = fresh n bads
            in
            (Lam n' e t, bads)
        replace' _ _ _ t = (t, [])


-- Replace a whole list of names with new ones in an Expr via folding.
replaceList :: Expr -> [Name] -> [Name] -> [Name] -> Expr
replaceList expr env olds news = foldl (\e (n, n') -> replace e env n n')
                                      expr $ zip olds news

-- Generates a fresh name given an old name and a list of INVALID names
fresh :: Name -> [Name] -> Name
fresh o ns = let r = foldl (\s c -> if s == c then s ++ [head c] else s) o ns
             in if r `elem` ns then fresh r ns else r 

-- Generates a list of fresh names. Ensures no conflict with original old list.
freshList :: [Name] -> [Name] -> [Name]
freshList os ns = snd $ foldl (\(bads, ress) o -> let o' = fresh o bads
                                                  in (o':bads, ress++[o']))
                              (ns ++ os, []) os

-- Generates a list of fresh names based on a name. Ensuring no conflict with original old list or new names.
numFresh :: Name -> Int -> [Name] -> [Name]
numFresh n 0 ns = []
numFresh n i ns = let f = fresh n ns in f:numFresh n (i - 1) (f:ns) 

-- Returns free variables of an expression with respect to list of bounded vars.
freeVars :: Manipulatable Expr m => [Name] -> m -> [Name]
freeVars bv e = snd . eval'' (freeVars') e $ (bv, [])
    where
        freeVars' :: ([Name], [Name]) -> Expr -> ([Name], [Name])
        freeVars' (bv, fr) (Var n' _) = if n' `elem` bv then ([], []) else ([], [n'])
        freeVars' (bv, fr) (Lam n' _ _) = ([n'], [])
        freeVars' _ _ = ([], [])

--Takes e e1 e2.  In e, replaces all occurences of e1 with e2
replaceM :: (Manipulatable e m, Eq e) => m -> e -> e -> m
replaceM e e1 e2 = modify (\e' -> if e1 == e' then e2 else e') e

--Find the number of Expr or Type's in a Manipulatable type.
countExpr :: Manipulatable Expr m => m -> Int
countExpr e = Mon.getSum . evalE (\_ -> Mon.Sum 1) $ e

countTypes :: Manipulatable Type m => m -> Int
countTypes t = Mon.getSum . evalT (\_ -> Mon.Sum 1) $ t
