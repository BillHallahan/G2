module G2.Internals.Initialization.Defunctionalizor
    (defunctionalize) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.SymLinks as SymLinks

import Data.List
import Data.Maybe
import qualified Data.Map as M

import Debug.Trace

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

defunctionalize :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, TypeEnv, NameGen, FuncInterps)
defunctionalize eenv tenv ng = defunctionalize' eenv tenv ng (FuncInterps M.empty)

defunctionalize' :: ExprEnv -> TypeEnv -> NameGen -> FuncInterps -> (ExprEnv, TypeEnv, NameGen, FuncInterps)
defunctionalize' eenv tenv ng ft =
    case leadingHigherOrderTypes eenv tenv of
            (t:_) -> 
                let 
                    (eenv', tenv', ng', ft') = useApplyType eenv tenv ng ft t
                in
                trace ("adjust type = " ++ show t) $ defunctionalize' eenv' tenv' ng' ft'
            _ -> (eenv, tenv, ng, ft)

-- Given a state and a leading higher order function type
-- adjusts the state to use apply types instead.
-- This involves:
--   (1) Creating the apply datatype, and an apply constructor for each function of that type
--   (2) Create an apply function
--   (3) Adjust all relevant higher order functions
useApplyType :: ExprEnv -> TypeEnv -> NameGen -> FuncInterps -> Type -> (ExprEnv, TypeEnv, NameGen, FuncInterps)
useApplyType eenv tenv ng ft (t@(TyFun _ _)) =
    let
        funcs = passedToHigherOrder eenv t

        --apply data type
        (applyTypeName, ng2) = freshSeededName (Name "ApplyType" Nothing 0) ng
        applyTypeCon = TyConApp applyTypeName []
        
        (applyConsNames, ng3) = freshSeededNames (map (\e -> case e of
                                                            Var (Id n _) -> n
                                                            _ -> Name "ApplyCon" Nothing 0) funcs) ng2
        applyDCs = map (\n -> DataCon n applyTypeCon []) applyConsNames
        applyTypeAlg = AlgDataTy [] applyDCs

        namesToFuncs = zip applyConsNames funcs 

        --function
        (applyFuncName, ng4) = freshSeededName (Name "applyFunc" Nothing 0) ng3
        args = argList t
        (applyFunc, ng5) = createApplyFunc args applyTypeName namesToFuncs ng4

        --adjustment
        higherNameExpr = higherOrderOfTypeFuncNames eenv t
        higherNameExprArgs = map (\(n, e) -> (n, e, higherOrderArgs e)) higherNameExpr


        newFuncs_interps = FuncInterps $ M.fromList . catMaybes . map (\(a, n) -> 
                                                case n of
                                                    Var (Id n' _) -> Just (a, (n', StdInterp))
                                                    _ -> Nothing) $ namesToFuncs

        eenv' = foldr (\(n, e, a) -> updateArgRefs n t applyTypeCon applyFuncName e a) eenv higherNameExprArgs

        eenv'' = foldr (\(n, e) -> modifyASTs (sndAppReplaceEx e n t applyTypeCon)) eenv' namesToFuncs

        eenv''' = modifyASTs (applyTypeReplace t applyTypeCon) eenv''

        eenv'''' = adjustLambdas t applyTypeCon eenv'''

        tenv' = modifyTypeEnv t applyTypeCon tenv
    in
    ( E.insert applyFuncName applyFunc eenv''''
    , M.insert applyTypeName applyTypeAlg tenv'
    , ng5
    , unionFuncInterps newFuncs_interps ft)
    where
        argList :: Type -> [Type]
        argList (TyFun ty ty') = ty:argList ty'
        argList ty = [ty]

        updateArgRefs :: FuncName -> Type -> Type -> FuncName -> Expr -> [(FuncName, Type)] -> ExprEnv -> ExprEnv
        updateArgRefs na ty t' fn e ns eenv =
            let
                e' = updateArgRefs' ty t' fn e ns
            in
            E.insertPreserving na e' eenv

        updateArgRefs' :: Type -> Type -> FuncName -> Expr -> [(FuncName, Type)] -> Expr
        updateArgRefs' _ _ _ e [] = e
        updateArgRefs' ty at fn e ((n, t'):ns) =
            let
                funcType = TyFun at ty

                e' = fstAppReplace fn n funcType t' e
                e'' = sndAppReplace fn n t' at e'
            in
            if ty == t' then updateArgRefs' ty at fn e'' ns else updateArgRefs' ty at fn e ns

useApplyType _ _ _ _ t = error ("Non-TyFun type " ++ show t ++ " given to createApplyType.")

--Creates the apply function
createApplyFunc :: [Type] -> ApplyTypeName -> [(Name, Expr)] -> NameGen -> (Expr, NameGen)
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
                        (Alt (DataAlt (DataCon n (TyConApp applyTypeName []) []) [new])
                             (foldr (\i' e' -> App e' i') e args_vars)))
                        (zip namesToFuncs (map (\n -> Id n case_expr_type) new_names))
        case_final = Case case_expr (Id top case_expr_type) case_matches

        arg_lams = foldr (\(a, t) e -> Lam (Id a t) e) case_final (zip args ts)
    in
    (Lam apply_arg_id arg_lams, r5)

-- This adjusts for when the function with the given name is in the first position in an app
-- This means that the function is being called
-- We change the call to the function, to a call to the apply function, and pass in the correct constructor
fstAppReplace :: FuncName -> FuncName -> Type -> Type -> Expr -> Expr
fstAppReplace fn n tn ty = modify (fstAppReplace')
    where
        fstAppReplace' :: Expr -> Expr
        fstAppReplace' a@(App e e') =
            if e == Var (Id n ty) then App (App (Var (Id fn tn)) e) e' else a
        fstAppReplace' e = e

-- This adjusts for when the function with the given name is in the second position in an app
-- This means that the function is being passed
-- It simply swaps the type of the function, from a function type to an applytype
sndAppReplace :: FuncName -> FuncName -> Type -> Type -> Expr -> Expr
sndAppReplace fn n ty at = modify (sndAppReplace')
    where
        sndAppReplace' :: Expr -> Expr
        sndAppReplace' a@(App e e') =
            if e' == Var (Id fn ty) then App e (Var (Id n at)) else a
        sndAppReplace' e = e

sndAppReplaceEx :: Expr -> FuncName -> Type -> Type -> Expr -> Expr
sndAppReplaceEx repEx n ty at = modify (sndAppReplaceEx')
    where
        sndAppReplaceEx' :: Expr -> Expr
        sndAppReplaceEx' a@(App e e') =
            if e' == repEx then App e (Data (DataCon n at [])) else a
        sndAppReplaceEx' e = e

-- Given a TyFun type, an apply type, and a type, replaces all of the TyFun types with the apply type
applyTypeReplace :: Type -> Type -> Type -> Type
applyTypeReplace tOld tNew t@(TyFun t'@(TyFun _ _) t'') =
    if t' == tOld then
        TyFun tNew t''
    else
        t
applyTypeReplace _ _ t = t

-- Get all function types that are passed into any function
leadingHigherOrderTypes :: ExprEnv -> TypeEnv -> [Type]
leadingHigherOrderTypes eenv tenv =
    let
        higherTExprEnv = higherOrderTypesTEnv $ tenv
        higherExprEnv = map typeOf . higherOrderFuncsExprEnv  $ eenv
    in
    nub . concatMap leading $ higherTExprEnv ++ higherExprEnv
    where
        leading :: Type -> [Type]
        leading = eval leading'

        leading' :: Type -> [Type]
        leading' (TyFun t@(TyFun _ _) _) = [t]
        leading' _ = []

-- Get higher order types from the type environment
higherOrderTypesTEnv :: TypeEnv -> [Type]
higherOrderTypesTEnv tenv = filter (higherOrderFuncType) (map (typeOf :: Type -> Type) . containedASTs $ M.elems tenv)

-- Get higher order functions from the expression environment
higherOrderFuncsExprEnv :: E.ExprEnv -> [Expr]
higherOrderFuncsExprEnv = filter (higherOrderFunc) . E.elems

-- Returns whether the expr is a higher order function
higherOrderFunc :: Expr -> Bool
higherOrderFunc e = higherOrderFuncType $ typeOf e

-- Returns whether the type is for a higher order function
higherOrderFuncType :: Type -> Bool
higherOrderFuncType (TyFun (TyFun _ _) _) = True
higherOrderFuncType (TyFun t t') = higherOrderFuncType t || higherOrderFuncType t'
higherOrderFuncType _ = False

-- Given a function type t, gets a list of:
-- (1) all functions of type t from the expression environment
-- (2) all expresions of type t that are passed into a higher order function,
--     somewhere in the expression environment
passedToHigherOrder :: E.ExprEnv -> Type -> [Expr]
passedToHigherOrder eenv t =
    let
        funcs = map (\n -> Var $ Id n t) (functionNamesOfType eenv t)
        part_lams = concatMap (\e -> higherOrderArg e (typeOf e)) (E.elems eenv)
    in
    nub (funcs ++ part_lams)
    where
        higherOrderArg :: Expr -> Type -> [Expr]
        higherOrderArg (App f a) (TyFun t'@(TyFun _ _) t'') = f:(higherOrderArg f t' ++ higherOrderArg a t'')
        higherOrderArg (App _ a) (TyFun _ t') = higherOrderArg a t'
        higherOrderArg _ _ = []

-- Given an expression environment, gets the names and expressions of all higher order functions
-- that accept the given type
higherOrderOfTypeFuncNames :: E.ExprEnv -> Type -> [(FuncName, Expr)]
higherOrderOfTypeFuncNames eenv ty =
    nub . filter (\(_, e) -> ty `elem` functionsAccepted e) . E.toExprList $ eenv
    where
        -- Returns a list of all function types that must be passed to the given function
        functionsAccepted :: Expr -> [Type]
        functionsAccepted = evalASTs functionsAccepted' . typeOf
            where
                functionsAccepted' (TyFun t@(TyFun _ _) _) = [t]
                functionsAccepted' _ = []

-- Given a higher order function, returns the names and types of all higher order arguments
higherOrderArgs :: Expr -> [(FuncName, Type)]
higherOrderArgs l@(Lam (Id n _) e) =
    case typeOf l of
        TyFun t@(TyFun _ _) _ -> (n, t):higherOrderArgs e
        _ -> higherOrderArgs e
higherOrderArgs _ = []

-- Returns all function names of the given type
functionNamesOfType :: E.ExprEnv -> Type -> [FuncName]
functionNamesOfType eenv t =
    map fst . filter (\(n, e') -> not (E.isSymbolic n eenv) && typeOf e' == t) . E.toExprList $ eenv

-- Changes all Lambda id's of Type rt to Type at
adjustLambdas :: (ASTContainer m Expr) => Type -> Type -> m -> m
adjustLambdas rt at = modifyASTs (adjustLambdas')
    where
        adjustLambdas' :: Expr -> Expr
        adjustLambdas' l@(Lam (Id n t) e) = if t == rt then Lam (Id n at) e else l
        adjustLambdas' e = e

----
-- Updating the type environment
----

modifyTypeEnv :: Type -> Type -> TypeEnv -> TypeEnv
modifyTypeEnv t nt = M.map (modifyTypeEnv' t nt)

modifyTypeEnv' :: Type -> Type -> AlgDataTy -> AlgDataTy
modifyTypeEnv' t nt (AlgDataTy n dc) = AlgDataTy n (map (modifyDC t nt) dc)

modifyDC :: Type -> Type -> DataCon -> DataCon
modifyDC t nt (DataCon n t' ts) = DataCon n (modifyASTs (applyTypeReplace t nt) t') (modifyASTs (rep t nt) ts)

rep :: Type -> Type -> Type -> Type
rep t nt c = if t == c then nt else c
