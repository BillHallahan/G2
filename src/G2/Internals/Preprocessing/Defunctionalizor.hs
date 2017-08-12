module G2.Internals.Preprocessing.Defunctionalizor 

(defunctionalize) where

import G2.Internals.Language
import qualified G2.Internals.Language.SymLinks as SymLinks

import Data.List
import Data.Maybe
import qualified Data.Map as M

{-Defunctionalizor

We need to eliminate higher order functions to
enable a translation to SMT formulas.

This can be done via Defunctionalization, described by Reynolds in
http://cs.au.dk/~hosc/local/HOSC-11-4-pp363-397.pdf

In short, each call to a higher order functions (a -> b) -> c is identified.
For each a, b pair, a new datatype A_B, and fresh function,
apply_a_b :: A_B -> a -> b, is created.
-}

type FuncName = Name
type ApplyTypeName = Name

defunctionalize :: State -> State
defunctionalize s =
    case leadingHigherOrderTypes s of
            (t:_) -> defunctionalize . useApplyType s $ t
            _ -> s

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
        (applyTypeName, r2) = freshSeededName (Name "ApplyType" Nothing 0) (all_names s)
        (applyConsNames, r3) = freshSeededNames (take (length funcs) . repeat $ Name "ApplyType" Nothing 0) r2
        applyTypeAlg = TyAlg applyConsNames []
        applyTypeCon = TyConApp applyTypeName []

        namesToFuncs = zip applyConsNames funcs 

        --function
        (applyFuncName, r4) = freshSeededName (Name "applyFunc" Nothing 0) r3
        args = argList t
        (applyFunc, r5) = createApplyFunc args applyTypeName namesToFuncs r4

        --adjustment
        higherNameExpr = higherOrderOfTypeFuncNames (expr_env s) t
        higherNameExprArgs = map (\(n, e) -> (n, e, higherOrderArgs e)) higherNameExpr

        funcsInSLT = funcsInSymLink t (sym_links s)

        newCurr_expr = foldr (\n -> exprReplace (Var $ Id n t) (Var $ Id n applyTypeCon)) (curr_expr s) funcsInSLT

        newFuncs_interps = FuncInterps $ M.fromList . catMaybes . map (\(a, n) -> 
                                                case n of
                                                    Var (Id n _) -> Just (a, (n, StdInterp))
                                                    _ -> Nothing) $ namesToFuncs

        s2 = foldr (\(n, e, a) -> updateArgRefs n t applyTypeCon applyFuncName e a) (s {all_names = r5}) higherNameExprArgs

        s3 = modifyASTs (applyTypeReplace t applyTypeCon) (s2 {curr_expr = newCurr_expr})

    in
    s3 { expr_env = M.insert applyFuncName applyFunc (expr_env s3)
        , type_env = M.insert applyTypeName applyTypeAlg (type_env s3)
        , sym_links = adjustSymLinks t applyTypeCon (sym_links s3)
        , func_table = unionFuncInterps newFuncs_interps (func_table s3)
    }
    where
        argList :: Type -> [Type]
        argList (TyFun t t') = t:argList t'
        argList t = [t]

        updateArgRefs :: FuncName -> Type -> Type -> FuncName -> Expr -> [(FuncName, Type)] -> State -> State
        updateArgRefs n t t' fn e ns s =
            let
                e' = updateArgRefs' t t' fn e ns
            in
            s {expr_env = M.insert n e' (expr_env s)}

        updateArgRefs' :: Type -> Type -> FuncName -> Expr -> [(FuncName, Type)] -> Expr
        updateArgRefs' _ _ _ e [] = e
        updateArgRefs' t at fn e ((n, t'):ns) =
            let
                funcType = TyFun at t

                e' = fstAppReplace funcType fn n t' e
                e'' = sndAppReplace n t' at e'
            in
            if t == t' then updateArgRefs' t at fn e'' ns else updateArgRefs' t at fn e ns

        -- This adjusts for when the function with the given name is in the first position in an app
        -- This means that the function is being called
        -- We change the call to the function, to a call to the apply function, and pass in the correct constructor
        fstAppReplace :: Type -> FuncName -> FuncName -> Type -> Expr -> Expr
        fstAppReplace tn fn n t = modify (fstAppReplace' tn fn n t)
            where
                fstAppReplace' :: Type -> FuncName -> FuncName -> Type -> Expr -> Expr
                fstAppReplace' tn fn n t a@(App e e') =
                    if e == Var (Id n t) then App (App (Var (Id fn tn)) e) e' else a
                fstAppReplace' _ _ _ _ e = e

        -- This adjusts for when the function with the given name is in the second position in an app
        -- This means that the function is being passed
        -- It simply swaps the type of the function, from a function type to an applytype
        sndAppReplace :: FuncName -> Type -> Type -> Expr -> Expr
        sndAppReplace n t at = modify (sndAppReplace')
            where
                sndAppReplace' :: Expr -> Expr
                sndAppReplace' a@(App e e') =
                    if e' == Var (Id n t) then App e (Var (Id n at)) else a
                sndAppReplace' e = e

        -- Gets the names of all functions in the symbolic link table, that are of the given type
        funcsInSymLink :: Type -> SymLinks -> [FuncName]
        funcsInSymLink t = SymLinks.names . SymLinks.filter (\(_, t', _) -> t == t')

        -- In the symbolic link table, changes all Types rt to Type at
        adjustSymLinks :: Type -> Type -> SymLinks -> SymLinks
        adjustSymLinks rt at = SymLinks.map (\(n, t, i) -> (n, if t == rt then at else t, i))

useApplyType _ t = error ("Non-TyFun type " ++ show t ++ " given to createApplyType.")

--Creates the apply function
createApplyFunc :: [Type] -> ApplyTypeName -> [(Name, Expr)] -> Renamer -> (Expr, Renamer)
createApplyFunc ts applyTypeName namesToFuncs r =
    let
        (new_names, r2) = freshSeededNames (replicate (length namesToFuncs) (Name "apply_match" Nothing 0)) r
        (top, r3) = freshName r2
        (apply_arg, r4) = freshSeededName (Name "apply_" Nothing 0) r3
        (args, r5) = freshSeededNames (replicate (length ts - 1) (Name "i" Nothing 0)) r4
        args_vars = map (\(a, t) -> Var $ Id a t) (zip args ts)

        case_expr_type = TyConApp applyTypeName []
        apply_arg_id = Id apply_arg case_expr_type

        case_expr = Var apply_arg_id 
        case_matches = map (\((n, e), new) ->
                        (Alt (DataAlt $ DataCon n (TyConApp applyTypeName []) [])
                             [new]
                             (foldr (\i' e' -> App e' i') e args_vars)))
                        (zip namesToFuncs (map (\n -> Id n case_expr_type) new_names))
        case_final = Case case_expr (Id top case_expr_type) case_matches

        arg_lams = foldr (\(a, t) e -> Lam (Id a t) e) case_final (zip args ts)
    in
    (Lam apply_arg_id arg_lams, r5)

-- In e, replaces all eOld with eNew
exprReplace :: Expr -> Expr -> Expr -> Expr
exprReplace eOld eNew e =
    if e == eOld
        then modifyChildren (exprReplace eOld eNew) eNew 
        else modifyChildren (exprReplace eOld eNew) e

-- Given a TyFun type, an apply type, and a type, replaces all of the TyFun types with the apply type
applyTypeReplace :: Type -> Type -> Type -> Type
applyTypeReplace tOld tNew t@(TyFun t'@(TyFun _ _) t'') =
    if t' == tOld then
        TyFun tNew t''
    else
        t
applyTypeReplace _ _ t = t

-- Get all function types that are passed into any function
leadingHigherOrderTypes :: State -> [Type]
leadingHigherOrderTypes s =
    let
        higherTExprEnv = higherOrderTypesTEnv . type_env $ s
        higherExprEnv = map exprType . higherOrderFuncsExprEnv . expr_env $ s
    in
    nub . concatMap leading $ higherTExprEnv ++ higherExprEnv
    where
        leading :: Type -> [Type]
        leading = eval leading'

        leading' :: Type -> [Type]
        leading' (TyFun t@(TyFun _ _) _) = [t]
        leading' _ = []

-- Given a function type t, gets a list of:
-- (1) all functions of type t from the expression environment
-- (2) all expresions of type t that are passed into a higher order function,
--     somewhere in the expression environment
passedToHigherOrder :: ExprEnv -> Type -> [Expr]
passedToHigherOrder eenv t =
    let
        funcs = map (\n -> Var $ Id n t) (functionNamesOfType eenv t)
        part_lams = concatMap (\e -> higherOrderArg e (exprType e)) (M.elems eenv)
    in
    nub (funcs ++ part_lams)
    where
        higherOrderArg :: Expr -> Type -> [Expr]
        higherOrderArg (App f a) (TyFun t'@(TyFun _ _) t'') = f:(higherOrderArg f t' ++ higherOrderArg a t'')
        higherOrderArg (App _ a) (TyFun _ t') = higherOrderArg a t'
        higherOrderArg _ _ = []

-- Given an expression environment, gets the names and expressions of all higher order functions
-- that accept the given type
higherOrderOfTypeFuncNames :: ExprEnv -> Type -> [(FuncName, Expr)]
higherOrderOfTypeFuncNames eenv ty =
    nub . filter (\(_, e) -> ty `elem` functionsAccepted e) . M.toList $ eenv
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
higherOrderArgs :: Expr -> [(FuncName, Type)]
higherOrderArgs l@(Lam (Id n _) e) =
    case exprType l of
        TyFun t@(TyFun _ _) _ -> (n, t):higherOrderArgs e
        _ -> higherOrderArgs e
-- higherOrderArgs (Lam n e (TyFun t@(TyFun _ _) _)) = (n, t):higherOrderArgs e
higherOrderArgs _ = []

-- Returns all function names of the given type
functionNamesOfType :: ExprEnv -> Type -> [FuncName]
functionNamesOfType eenv t =
    map fst . filter (\(_, e') -> exprType e' == t) . M.assocs $ eenv

-- Get higher order functions from the expression environment
higherOrderFuncsExprEnv :: ExprEnv -> [Expr]
higherOrderFuncsExprEnv = filter (higherOrderFunc) . M.elems

-- Get higher order types from the type environment
higherOrderTypesTEnv :: TypeEnv -> [Type]
higherOrderTypesTEnv tenv = filter (higherOrderFuncType) (map tyArgType . containedASTs $ M.elems tenv)

-- Returns whether the expr is a higher order function
higherOrderFunc :: Expr -> Bool
higherOrderFunc e = higherOrderFuncType . exprType $ e

-- Returns whether the type is for a higher order function
higherOrderFuncType :: Type -> Bool
higherOrderFuncType (TyFun (TyFun _ _) _) = True
higherOrderFuncType (TyFun t t') = higherOrderFuncType t || higherOrderFuncType t'
higherOrderFuncType (TyApp t t') = higherOrderFuncType t || higherOrderFuncType t'
higherOrderFuncType _ = False