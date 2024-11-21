{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module G2.Initialization.MkCurrExpr ( mkCurrExpr
                                    , checkReaches
                                    , findFunc
                                    , instantiateArgTypes ) where

import G2.Config
import G2.Language
import qualified G2.Language.ExprEnv as E

import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Text as T
import qualified Data.HashMap.Lazy as HM 

mkCurrExpr :: Maybe T.Text -> Maybe T.Text -> Id
           -> TypeClasses -> NameGen -> ExprEnv -> TypeEnv
           -> KnownValues -> Config -> (Expr, [Id], [Expr], Maybe Coercion, NameGen)
mkCurrExpr m_assume m_assert f@(Id (Name _ m_mod _ _) _) tc ng eenv tenv kv config =
    case E.lookup (idName f) eenv of
        Just ex ->
            let
                var_ex = Var (Id (idName f) (typeOf ex))
                (m_coer, coer_var_ex) = coerceRetNewTypes tenv var_ex

                -- -- We refind the type of f, because type synonyms get replaced during the initializaton,
                -- -- after we first got the type of f.
                (app_ex, is, typsE, ng') =
                    if instTV config == InstBefore
                        then mkMainExpr tc kv ng coer_var_ex
                        else mkMainExprNoInstantiateTypes coer_var_ex ng
                var_ids = map Var is

                (name, ng'') = freshName ng'
                id_name = Id name (typeOf app_ex)
                var_name = Var id_name

                assume_ex = mkAssumeAssert (Assume Nothing) m_assume m_mod (typsE ++ var_ids) var_name var_name eenv
                assert_ex = mkAssumeAssert (Assert Nothing) m_assert m_mod (typsE ++ var_ids) assume_ex var_name eenv

                retsTrue_ex = if returnsTrue config then retsTrue assert_ex else assert_ex

                let_ex = Let [(id_name, app_ex)] retsTrue_ex
            in
            (let_ex, is, typsE, m_coer, ng'')
        Nothing -> error "mkCurrExpr: Bad Name"
-- | If a function we are symbolically executing returns a newtype wrapping a function type, applies a coercion to the function.
-- For instance, given:
-- @
-- newtype F = F (Int -> Int) 

-- f :: Int -> F
-- f y = F (\x -> x + y)
-- @
--
-- This allows symbolic execution to find an input/output example:
--  @
-- ((coerce (f :: Int -> F)) :: Int -> Int -> Int) (0) (1) = 1
-- @
coerceRetNewTypes :: TypeEnv -> Expr -> (Maybe Coercion, Expr)
coerceRetNewTypes tenv e =
    let
        t = typeOf e
        rt = returnType e
        c = coerce_to rt
        c_rt = replace_ret_ty c t
        coer = t :~ c_rt
    in
    if rt == c then (Nothing, e) else (Just coer, Cast e coer) 
    where
        coerce_to t | TyCon n _:ts <- unTyApp t
                    , Just (NewTyCon { bound_ids = bis, rep_type = rt }) <- HM.lookup n tenv
                    , hasFuncType $ PresType rt = 
                        coerce_to $ foldl' (\rt_ (b, bt) -> retype b bt rt_) rt (zip bis ts)
                    | otherwise = t

        replace_ret_ty c (TyForAll i t) = TyForAll i $ replace_ret_ty c t
        replace_ret_ty c (TyFun t t') = TyFun t $ replace_ret_ty c t'
        replace_ret_ty c _ = c

mkMainExpr :: TypeClasses -> KnownValues -> NameGen -> Expr -> (Expr, [Id], [Expr], NameGen)
mkMainExpr tc kv ng ex =
    let
        typs = spArgumentTypes ex

        (typsE, typs') = instantitateTypes tc kv typs

        (var_ids, is, ng') = mkInputs ng typs'
        
        app_ex = foldl' App ex $ typsE ++ var_ids
    in
    (app_ex, is, typsE, ng')

-- | This implementation aims to symbolically execute functions 
-- treating both types and value level argument as symbolic
mkMainExprNoInstantiateTypes :: Expr -> NameGen -> (Expr, [Id], [Expr], NameGen)
mkMainExprNoInstantiateTypes e ng = 
    let 
        argts = spArgumentTypes e
        anontype argt = 
            case argt of 
                AnonType _ -> True
                _ -> False
        (ats,nts) = partition anontype argts 
        -- We want to have symbolic types so we grab the type level arguments and introduce symbolic variables for them
        ns = map (\(NamedType (Id n _)) -> n) nts
        (ns', ng') = renameAll ns ng

        ntmap = HM.fromList $ zip ns ns' 
        -- We want to create a full list of symoblic variables with new names and put the symbolic variables into the expr env
        -- Type level arguments
        ntids = map (\(NamedType i) -> i) nts
        ntids' = renames ntmap ntids

        -- Value level arguments
        ats' = map argTypeToType ats
        (atsToIds,ng'') = freshIds ats' ng'
        atsToIds' = renames ntmap atsToIds

        all_ids = ntids' ++ atsToIds'
        ars = map (Type . TyVar) ntids' ++ map Var atsToIds'
        app_ex = foldl' App (renames ntmap e) ars
    in  (app_ex, all_ids, [],ng'')


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
    case findFunc f [m_mod] eenv of
        Left (f', _) -> 
            let
                app_ex = foldl' App (Var f') (var_ids ++ [pre_ex])
            in
            p app_ex inter
        Right s -> error s
mkAssumeAssert _ Nothing _ _ e _ _ = e

retsTrue :: Expr -> Expr
retsTrue e = Assert Nothing e e

findFunc :: T.Text -> [Maybe T.Text] -> ExprEnv -> Either (Id, Expr) String
findFunc s m_mod eenv =
    let
        match = E.toExprList $ E.filterWithKey (\n _ -> nameOcc n == s) eenv
    in
    case match of
        [] -> Right $ "No functions with name " ++ (T.unpack s)
        [(n, e)] -> Left (Id n (typeOf e) , e)
        pairs -> case filter (\(n, _) -> nameModule n `elem` m_mod) pairs of
                    [(n, e)] -> Left (Id n (typeOf e), e)
                    [] -> Right $ "No function with name " ++ (T.unpack s) ++ " in available modules"
                    _ -> Right $ "Multiple functions with same name " ++ (T.unpack s) ++
                                " in available modules"

instantiateArgTypes :: TypeClasses -> KnownValues -> Expr -> ([Expr], [Type])
instantiateArgTypes tc kv e =
    let
        typs = spArgumentTypes e
    in
    instantitateTypes tc kv typs

instantitateTypes :: TypeClasses -> KnownValues -> [ArgType] -> ([Expr], [Type])
instantitateTypes tc kv ts = 
    let
        tv = mapMaybe (\case NamedType i -> Just i; AnonType _ -> Nothing) ts

        -- Get non-TyForAll type reqs, identify typeclasses
        ts' = mapMaybe (\case AnonType t -> Just t; NamedType _ -> Nothing) ts
        tcSat = snd $ mapAccumL (\ts'' i ->
                                let
                                    sat = satisfyingTCTypes kv tc i ts''
                                    pt = pickForTyVar kv sat
                                in
                                (replaceTyVar (idName i) pt ts'', (i, pt))) ts' tv

        -- Get dictionary arguments
        vi = mapMaybe (instantiateTCDict tc tcSat) ts'

        ex = map (Type . snd) tcSat ++ vi
        tss = filter (not . isTypeClass tc)
            . foldr (uncurry replaceASTs) ts'
            $ map (\(i, t) -> (TyVar i, t)) tcSat
    in
    (ex, tss)

-- From the given list, selects the Type to instantiate a TyVar with
pickForTyVar :: KnownValues -> [Type] -> Type
pickForTyVar kv ts
    | Just t <- find ((==) (tyInt kv)) ts = t
    | t:_ <- ts = t
    | otherwise = error "No type found in pickForTyVar"


instantiateTCDict :: TypeClasses -> [(Id, Type)] -> Type -> Maybe Expr
instantiateTCDict tc it tyapp@(TyApp _ t) | TyCon n _ <- tyAppCenter tyapp =
    let
        t' = applyTypeMap (M.fromList $ map (\(Id ni _, ti) -> (ni,ti)) it) t
    in
    return . Var =<< lookupTCDict tc n t'
instantiateTCDict _ _ _ = Nothing

checkReaches :: ExprEnv -> KnownValues -> Maybe T.Text -> Maybe T.Text -> ExprEnv
checkReaches eenv _ Nothing _ = eenv
checkReaches eenv kv (Just s) m_mod =
    case findFunc s [m_mod] eenv of
        Left (Id n _, e) -> E.insert n (Assert Nothing (mkFalse kv) e) eenv
        Right err -> error  err
