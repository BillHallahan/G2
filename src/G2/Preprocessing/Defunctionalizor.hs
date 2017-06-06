module G2.Preprocessing.Defunctionalizor (defunctionalize) where

import Data.List
import qualified Data.Map as M
import Data.Maybe

import G2.Core.Language
import G2.Core.Utils

import G2.Lib.CoreManipulator

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function,
apply_a_b :: A_B -> a -> b, is created.
-}

defunctionalize :: State -> State
defunctionalize s =
    case leadingHigherOrderTypes s of
            (t:_) -> defunctionalize . useApplyType s $ t
            otherwise -> s

-- Given a state and a leading higher order function type
-- adjusts the state to use apply types instead.
-- This involves:
--   (1) Creating the apply datatype, and an apply constructor for each function of that type
--   (2) Create an apply function
--   (3) Adjust all relevant higher order functions
useApplyType :: State -> Type -> State
useApplyType s (t@(TyFun _ _)) =
    let
        funcs = passedToHigherOrder (expr_env s) t

        --apply data type
        applyTypeName = freshSeededName "ApplyType" s
        args = argList t
        applyConsNames = freshSeededNameList (take (length funcs) . repeat $ "apply") s
        applyTypeAlg = TyAlg applyTypeName (map (\n -> DataCon n (-1) (TyConApp applyTypeName []) []) applyConsNames)
        applyTypeCon = TyConApp applyTypeName []

        namesToFuncs = zip applyConsNames funcs 
        funcsToNames = map (\(a, b) -> (b, a)) namesToFuncs

        --function
        applyFuncName = freshSeededName "applyFunc" s
        applyFunc = createFunc args applyTypeName namesToFuncs s
        applyFuncType = TyFun applyTypeCon t

        --adjustment
        higherNameExpr = higherOrderOfTypeFuncNames (expr_env s) t
        higherNameExprArgs = map (\(n, e) -> (n, e, higherOrderArgs e)) higherNameExpr

        funcsInSLT = funcsInSymLink t (sym_links s)

        newCurr_expr = foldr (\n -> exprReplace (Var n t) (Var n applyTypeCon)) (curr_expr s) funcsInSLT

        newFuncs_interps = M.fromList . catMaybes . map (\(a, n) -> 
                                                case n of
                                                    Var n t -> Just (a, (n, StdInterp))
                                                    otherwise -> Nothing) $ namesToFuncs

        s' = foldr (\(n, e, a) -> updateArgRefs n t applyTypeCon applyFuncType applyFuncName e a) s higherNameExprArgs

        s'' = modify (applyTypeReplace t applyTypeCon) (s' {curr_expr = newCurr_expr})

    in
    s'' { expr_env = M.insert applyFuncName applyFunc (expr_env s'')
        , type_env = M.insert applyTypeName applyTypeAlg (type_env s'')
        , sym_links = adjustSymLinks t applyTypeCon (sym_links s'')
        , func_interps = M.union newFuncs_interps (func_interps s'')
    }
    where
        --This creates the apply function
        createFunc :: [Type] -> Name -> [(Name, Expr)] -> State -> Expr
        createFunc ts applyTypeName namesToFuncs s =
            let
                ret_type = head . reverse $ ts

                new_names = freshSeededNameList (repeat "apply_match") s
                apply_arg = freshSeededName "apply_" s
                args = freshSeededNameList (replicate (length ts - 1) "i") s
                args_vars = map (\(a, t) -> Var a t) (zip args ts)

                case_expr = Var apply_arg (TyConApp applyTypeName [])
                case_matches = map (\((n, e), new) ->
                                (Alt ((DataCon n (-1) (TyConApp applyTypeName []) []), [new])
                                    , foldr (\i' e' -> App e' i') e args_vars))
                                (zip namesToFuncs new_names)
                case_final = Case case_expr case_matches ret_type

                arg_lams = foldr (\(a, t) e -> Lam a e (TyFun t (exprType e))) case_final (zip args ts)
            in
            Lam apply_arg arg_lams (TyFun (TyConApp applyTypeName []) (exprType arg_lams))

        argList :: Type -> [Type]
        argList (TyFun t t') = t:argList t'
        argList t = [t]

        updateArgRefs :: Name -> Type -> Type -> Type -> Name -> Expr -> [(Name, Type)] -> State -> State
        updateArgRefs n t t' ft fn e ns s =
            let
                e' = updateArgRefs' t t' ft fn e ns
                newExpr_env = M.insert n e' (expr_env s)
            in
            s {expr_env = newExpr_env}

        updateArgRefs' :: Type -> Type -> Type -> Name -> Expr -> [(Name, Type)] -> Expr
        updateArgRefs' _ _ _ _ e [] = e
        updateArgRefs' t at ft fn e ((n, t'):ns) =
            let
                e' = fstAppReplace ft fn (Var n t') e
                e'' = sndAppReplace (Var n t') (Var n at) e'
            in
            if t == t' then updateArgRefs' t at ft fn e'' ns else updateArgRefs' t at ft fn e ns

        -- This adjusts for when the function with the given name is in the first position in an app
        -- This means that the function is being called
        fstAppReplace :: Type -> Name -> Expr -> Expr -> Expr
        fstAppReplace tn fn eOld (Lam n e t) = Lam n (fstAppReplace tn fn eOld e) t
        fstAppReplace tn fn eOld (App e e') =
            if e == eOld then
                App (fstAppReplace tn fn eOld (App (Var fn tn) e)) (fstAppReplace tn fn eOld e')
            else
                App (fstAppReplace tn fn eOld e) (fstAppReplace tn fn eOld e')
        fstAppReplace tn fn eOld (Case e ae t) =
            Case (fstAppReplace tn fn eOld e) (map (\(a, e) -> (a, fstAppReplace tn fn eOld e)) ae) t
        fstAppReplace _ _ _ e = e

        -- This adjusts for when the function with the given name is in the second position in an app
        -- This means that the function is being passed
        sndAppReplace :: Expr -> Expr -> Expr -> Expr
        sndAppReplace eOld eNew (Lam n e t) = Lam n (sndAppReplace eOld eNew e) t
        sndAppReplace eOld eNew a@(App e e') =
            if e' == eOld then
                App (sndAppReplace eOld eNew e) (sndAppReplace eOld eNew eNew )
            else
                App (sndAppReplace eOld eNew e) (sndAppReplace eOld eNew e')
        sndAppReplace eOld eNew (Case e ae t) =
            Case (sndAppReplace eOld eNew e) (map (\(a, e) -> (a, sndAppReplace eOld eNew e)) ae) t
        sndAppReplace _ _ e = e

        -- Gets the names of all functions in the symbolic link table, that are of the given type
        funcsInSymLink :: Type -> SymLinkTable -> [Name]
        funcsInSymLink t = M.keys . M.filter (\(_, t', _) -> t == t')

        -- In the symbolic link table, changes all Types rt to Type at
        adjustSymLinks :: Type -> Type -> SymLinkTable -> SymLinkTable
        adjustSymLinks rt at = M.map (\(n, t, i) -> (n, if t == rt then at else t, i))

useApplyType _ t = error ("Non-TyFun type " ++ show t ++ " given to createApplyType.")

-- In e, replaces all eOld with eNew
exprReplace :: Expr -> Expr -> Expr -> Expr
exprReplace eOld eNew e = if e == eOld then exprReplace' eOld eNew eNew else exprReplace' eOld eNew e
    where
        exprReplace' :: Expr -> Expr -> Expr -> Expr
        exprReplace' eOld eNew (Lam n e t) = Lam n (exprReplace eOld eNew e) t
        exprReplace' eOld eNew (App e e') = App (exprReplace eOld eNew e) (exprReplace eOld eNew e')
        exprReplace' eOld eNew (Case e ae t) =
            Case (exprReplace eOld eNew e) (map (\(a, e) -> (a, exprReplace eOld eNew e)) ae) t
        exprReplace' _ _ e = e

-- Given a TyFun type, an apply type, and a type, replaces all of the TyFun types with the apply type
applyTypeReplace :: Type -> Type -> Type -> Type
applyTypeReplace tOld tNew t@(TyFun t'@(TyFun _ _) t'') =
    if t' == tOld then
        applyTypeReplace tOld tNew (TyFun tNew t'')
    else
        TyFun (applyTypeReplace tOld tNew t') (applyTypeReplace tOld tNew t'')
applyTypeReplace tOld tNew (TyApp t t') = TyApp (applyTypeReplace tOld tNew t) (applyTypeReplace tOld tNew t')
applyTypeReplace tOld tNew (TyConApp n ts) = TyConApp n (map (applyTypeReplace tOld tNew) ts)
applyTypeReplace tOld tNew (TyForAll n t) = TyForAll n (applyTypeReplace tOld tNew t)
applyTypeReplace _ _ t = t

-- Get all function types that are passed into any function
leadingHigherOrderTypes :: State -> [Type]
leadingHigherOrderTypes s =
    let
        higherTEenv = higherOrderTypesTEnv . type_env $ s
        higherEEnv = map exprType . higherOrderFuncsEEnv . expr_env $ s
    in
    nub . concatMap leading $ higherTEenv ++ higherEEnv
    where
        leading :: Type -> [Type]
        leading (TyFun t@(TyFun _ _) t') = t:(leading t ++ leading t')
        leading (TyFun t t') = leading t ++ leading t'
        leading (TyApp t t') = leading t ++ leading t'
        leading (TyConApp _ ts) = concatMap leading ts
        leading (TyAlg _ dc) = concatMap (\(DataCon _ _ t ts) -> leading t ++ concatMap leading ts) dc
        leading (TyForAll _ t) = leading t

-- Given a function type t, gets a list of:
-- (1) all functions of type t from the expression environment
-- (2) all expresions of type t that are passed into a higher order function,
--     somewhere in the expression environment
passedToHigherOrder :: EEnv -> Type -> [Expr]
passedToHigherOrder eenv t =
    let
        funcs = map (\n -> Var n t) (functionNamesOfType eenv t)
        part_lams = concatMap (\e -> higherOrderArg e (exprType e)) (M.elems eenv)
    in
    nub (funcs ++ part_lams)
    where
        higherOrderArg :: Expr -> Type -> [Expr]
        higherOrderArg (App f a) (TyFun t@(TyFun _ _) t') = f:(higherOrderArg f t ++ higherOrderArg a t')
        higherOrderArg (App _ a) (TyFun _ t) = higherOrderArg a t
        higherOrderArg _ _ = []

-- Given an expression environment, gets the names and expressions of all higher order functions
-- that accept the given type
higherOrderOfTypeFuncNames :: EEnv -> Type -> [(Name, Expr)]
higherOrderOfTypeFuncNames eenv t =
    nub . filter (\(n, e) -> t `elem` functionsAccepted e) . M.toList $ eenv
    where
        -- Returns a list of all function types that must be passed to the given function
        functionsAccepted :: Expr -> [Type]
        functionsAccepted = functionsAccepted' . exprType
            where
                functionsAccepted' (TyFun t@(TyFun _ _) t') = t:functionsAccepted' t'
                functionsAccepted' (TyApp t t') = functionsAccepted' t ++ functionsAccepted' t'
                functionsAccepted' (TyConApp _ ts) = concatMap functionsAccepted' ts
                functionsAccepted' (TyForAll _ t) = functionsAccepted' t
                functionsAccepted' _ = []

-- Given a higher order function, returns the names and types of all higher order arguments
higherOrderArgs :: Expr -> [(Name, Type)]
higherOrderArgs (Lam n e (TyFun t@(TyFun _ _) _)) = (n, t):higherOrderArgs e
higherOrderArgs (Lam _ e _) = higherOrderArgs e
higherOrderArgs _ = []

-- Returns all function names of the given type
functionNamesOfType :: EEnv -> Type -> [Name]
functionNamesOfType eenv t =
    map fst . filter (\(_, e') -> exprType e' == t) . M.assocs $ eenv

-- Get higher order functions from the expression environment
higherOrderFuncsEEnv :: EEnv -> [Expr]
higherOrderFuncsEEnv = filter (higherOrderFunc) . M.elems

-- Get higher order types from the type environment
higherOrderTypesTEnv :: TEnv -> [Type]
higherOrderTypesTEnv = filter (higherOrderFuncType) . M.elems

-- Returns whether the expr is a higher order function
higherOrderFunc :: Expr -> Bool
higherOrderFunc e = higherOrderFuncType . exprType $ e

-- Returns whether the type is for a higher order function
higherOrderFuncType :: Type -> Bool
higherOrderFuncType (TyFun (TyFun _ _) _) = True
higherOrderFuncType (TyFun t t') = higherOrderFuncType t || higherOrderFuncType t'
higherOrderFuncType (TyApp t t') = higherOrderFuncType t || higherOrderFuncType t'
higherOrderFuncType _ = False