module G2.Internals.Initialization.MkCurrExpr ( mkCurrExpr
                                              , checkReaches ) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import qualified G2.Internals.Language.ApplyTypes as AT

import Data.List
import Data.Maybe

mkCurrExpr :: Maybe String -> Maybe String -> String -> TypeClasses -> ApplyTypes -> NameGen -> ExprEnv -> Walkers -> KnownValues -> (Expr, [Id], NameGen)
mkCurrExpr m_assume m_assert s tc at ng eenv walkers kv =
    case findFunc s eenv of
        Left (f, ex) -> 
            let
                typs = argTys $ typeOf ex

                (typsE, typs') = instantitateTypes tc kv typs

                (var_ids, is, ng') = mkInputs at ng typs'
                
                var_ex = Var f
                app_ex = foldl' App var_ex $ typsE ++ var_ids

                strict_app_ex = mkStrict walkers app_ex

                (name, ng'') = freshName ng'
                id_name = Id name (typeOf strict_app_ex)
                var_name = Var id_name

                assume_ex = mkAssumeAssert Assume m_assume var_ids var_name var_name eenv
                assert_ex = mkAssumeAssert (Assert Nothing) m_assert var_ids assume_ex var_name eenv
                
                let_ex = Let [(id_name, strict_app_ex)] assert_ex
            in
            (let_ex, is, ng'')
        Right s' -> error s'

mkInputs :: ApplyTypes -> NameGen -> [Type] -> ([Expr], [Id], NameGen)
mkInputs _ ng [] = ([], [], ng)
mkInputs at ng (t:ts) =
    let
        (name, ng') = freshName ng

        (t', fv) =
            case AT.lookup t at of
                Just (t'', f) -> (TyConApp t'' [], App (Var f))
                Nothing -> (t, id)

        i = Id name t'
        var_id = fv $ Var i

        (ev, ei, ng'') = mkInputs at ng' ts
    in
    (var_id:ev, i:ei, ng'')

mkAssumeAssert :: (Expr -> Expr -> Expr) -> Maybe String -> [Expr] -> Expr -> Expr -> ExprEnv -> Expr
mkAssumeAssert p (Just f) var_ids inter pre_ex eenv =
    case findFunc f eenv of
        Left (f', _) -> 
            let
                app_ex = foldl' App (Var f') (var_ids ++ [pre_ex])
            in
            p app_ex inter
        Right s -> error s
mkAssumeAssert _ Nothing _ e _ _ = e

findFunc :: String -> ExprEnv -> Either (Id, Expr) String
findFunc s eenv =
    let
        match = E.toExprList $ E.filterWithKey (\(Name n _ _) _ -> n == s) eenv
    in
    case match of
        [(n, e)] -> Left (Id n (typeOf e) , e)
        _:_ -> Right $ "Multiple functions with name " ++ s
        [] -> Right $ "No functions with name " ++ s

-- distinguish between where a Type is being bound and where it is just the type (see argTys)
data TypeBT = B Id | T Type deriving (Show, Eq)

instantitateTypes :: TypeClasses -> KnownValues -> [TypeBT] -> ([Expr], [Type])
instantitateTypes tc kv ts = 
    let
        tv =  map (TyVar . typeTBId) $ filter (typeB) ts

        -- Get non-TyForAll type reqs, identify typeclasses
        ts' = map typeTBType $ filter (not . typeB) ts
        tcSat = satisfyingTCTypes tc ts'

        -- TyForAll type reqs
        tv' = map (\(i, ts'') -> (i, pickForTyVar kv ts'')) tcSat
        tvt = map (\(i, t) -> (TyVar i, t)) tv'
        -- Dictionary arguments
        vi = satisfyingTC tc ts' tv'-- map (\(_, (_, i)) -> i) tv'

        ex = map (Type . snd) tv' ++ map Var vi
        tss = filter (not . isTypeClass tc) $ foldr (uncurry replaceASTs) ts' tvt
    in
    (ex, tss)

-- From the given list, selects the Type to instantiate a TyVar with
pickForTyVar :: KnownValues -> [Type] -> Type
pickForTyVar kv ts
    | Just t <- find ((==) (tyInt kv)) ts = t
    | t:_ <- ts = t
    | otherwise = error "No type found in pickForTyVar"


argTys :: Type -> [TypeBT]
argTys (TyForAll (NamedTyBndr i) t') = (B i):argTys t'
argTys (TyFun t t') = (T t):argTys t'
argTys _ = []

typeTBId :: TypeBT -> Id
typeTBId (B i) = i
typeTBId (T t) = error "No Id in T"

typeTBType :: TypeBT -> Type
typeTBType (B _) = error "No type in B"
typeTBType (T t) = t 

typeB :: TypeBT -> Bool
typeB (B _) = True
typeB _ = False

checkReaches :: ExprEnv -> TypeEnv -> KnownValues -> Maybe String -> ExprEnv
checkReaches eenv _ _ Nothing = eenv
checkReaches eenv tenv kv (Just s) =
    case findFunc s eenv of
        Left (Id n _, e) -> E.insert n (Assert Nothing (mkFalse kv tenv) e) eenv
        Right err -> error err
