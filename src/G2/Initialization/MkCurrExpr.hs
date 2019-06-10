{-# LANGUAGE OverloadedStrings #-}

module G2.Initialization.MkCurrExpr ( mkCurrExpr
                                    , checkReaches
                                    , findFunc
                                    , instantiateArgTypes ) where

import G2.Config
import G2.Language
import qualified G2.Language.ExprEnv as E

import Data.List
import qualified Data.Text as T

mkCurrExpr :: Maybe T.Text -> Maybe T.Text -> Id
           -> TypeClasses -> NameGen -> ExprEnv -> Walkers
           -> KnownValues -> Config -> (Expr, [Id], [Expr], NameGen)
mkCurrExpr m_assume m_assert f@(Id (Name _ m_mod _ _) _) tc ng eenv walkers kv config =
    case E.lookup (idName f) eenv of
        Just ex ->
            let
                typs = spArgumentTypes ex

                (typsE, typs') = instantitateTypes tc kv typs

                (var_ids, is, ng') = mkInputs ng typs'
                
                var_ex = Var f
                app_ex = foldl' App var_ex $ typsE ++ var_ids

                -- strict_app_ex = app_ex
                strict_app_ex = if strict config then mkStrict walkers app_ex else app_ex

                (name, ng'') = freshName ng'
                id_name = Id name (typeOf strict_app_ex)
                var_name = Var id_name

                assume_ex = mkAssumeAssert (Assume Nothing) m_assume m_mod (typsE ++ var_ids) var_name var_name eenv
                assert_ex = mkAssumeAssert (Assert Nothing) m_assert m_mod (typsE ++ var_ids) assume_ex var_name eenv

                retsTrue_ex = if returnsTrue config then retsTrue assert_ex else assert_ex
                
                let_ex = Let [(id_name, strict_app_ex)] retsTrue_ex
            in
            (let_ex, is, typsE, ng'')
        Nothing -> error "mkCurrExpr: Bad Name"

mkInputs :: NameGen -> [Type] -> ([Expr], [Id], NameGen)
mkInputs ng [] = ([], [], ng)
mkInputs ng (t:ts) =
    let
        (name, ng') = freshName ng

        i = Id name t
        var_id = Var i

        (ev, ei, ng'') = mkInputs ng' ts
    in
    (var_id:ev, i:ei, ng'')

mkAssumeAssert :: (Expr -> Expr -> Expr) -> Maybe T.Text -> Maybe T.Text
               -> [Expr] -> Expr -> Expr -> ExprEnv -> Expr
mkAssumeAssert p (Just f) m_mod var_ids inter pre_ex eenv =
    case findFunc f m_mod eenv of
        Left (f', _) -> 
            let
                app_ex = foldl' App (Var f') (var_ids ++ [pre_ex])
            in
            p app_ex inter
        Right s -> error s
mkAssumeAssert _ Nothing _ _ e _ _ = e

retsTrue :: Expr -> Expr
retsTrue e = Assert Nothing e e

findFunc :: T.Text -> Maybe T.Text -> ExprEnv -> Either (Id, Expr) String
findFunc s m_mod eenv =
    let
        match = E.toExprList $ E.filterWithKey (\n _ -> nameOcc n == s) eenv
    in
    case match of
        [] -> Right $ "No functions with name " ++ (T.unpack s)
        [(n, e)] -> Left (Id n (typeOf e) , e)
        pairs -> case m_mod of
            Nothing -> Right $ "Multiple functions with same name. " ++
                               "Wrap the target function in a module so we can try again!"
            Just m -> case filter (\(n, _) -> nameModule n == Just m) pairs of
                [(n, e)] -> Left (Id n (typeOf e), e)
                [] -> Right $ "No function with name " ++ (T.unpack s) ++ " in module " ++ (T.unpack m)
                _ -> Right $ "Multiple functions with same name " ++ (T.unpack s) ++
                             " in module " ++ (T.unpack m)


instantiateArgTypes :: TypeClasses -> KnownValues -> Expr -> ([Expr], [Type])
instantiateArgTypes tc kv e =
    let
        typs = spArgumentTypes e
    in
    instantitateTypes tc kv typs

instantitateTypes :: TypeClasses -> KnownValues -> [ArgType] -> ([Expr], [Type])
instantitateTypes tc kv ts = 
    let
        tv = map (typeNamedId) $ filter (typeNamed) ts

        -- Get non-TyForAll type reqs, identify typeclasses
        ts' = map typeAnonType $ filter (not . typeNamed) ts
        tcSat = map (\i -> (i, satisfyingTCTypes kv tc i ts')) tv

        -- TyForAll type reqs
        tv' = map (\(i, ts'') -> (i, pickForTyVar kv ts'')) tcSat
        tvt = map (\(i, t) -> (TyVar i, t)) tv'
        -- Dictionary arguments
        vi = concatMap (uncurry (satisfyingTC tc ts')) tv'

        ex = map (Type . snd) tv' ++ vi
        tss = filter (not . isTypeClass tc) $ foldr (uncurry replaceASTs) ts' tvt
    in
    (ex, tss)

-- From the given list, selects the Type to instantiate a TyVar with
pickForTyVar :: KnownValues -> [Type] -> Type
pickForTyVar kv ts
    | Just t <- find ((==) (tyInt kv)) ts = t
    | t:_ <- ts = t
    | otherwise = error "No type found in pickForTyVar"

typeNamedId :: ArgType -> Id
typeNamedId (NamedType i) = i
typeNamedId (AnonType _) = error "No Id in T"

typeAnonType :: ArgType -> Type
typeAnonType (NamedType _) = error "No type in NamedType"
typeAnonType (AnonType t) = t 

typeNamed :: ArgType -> Bool
typeNamed (NamedType _) = True
typeNamed _ = False

checkReaches :: ExprEnv -> KnownValues -> Maybe T.Text -> Maybe T.Text -> ExprEnv
checkReaches eenv _ Nothing _ = eenv
checkReaches eenv kv (Just s) m_mod =
    case findFunc s m_mod eenv of
        Left (Id n _, e) -> E.insert n (Assert Nothing (mkFalse kv) e) eenv
        Right err -> error  err
