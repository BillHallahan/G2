{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Conversion ( addLHTC
                                      , addLHTCExprEnv
                                      , replaceVarTy
                                      , mergeLHSpecState
                                      , convertSpecTypeDict
                                      , convertLHExpr
                                      , specTypeToType
                                      , unsafeSpecTypeToType
                                      , symbolName
                                      , lhTCDict
                                      , numDict) where

import G2.Internals.Translation
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.KnownValues
import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Liquid.TCValues

import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine ()
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import  Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref

import Var hiding (tyVarName, isTyVar)

import Data.Coerce
import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T

import Debug.Trace

addLHTC :: (ASTContainer h Expr, ASTContainer t Expr) => State h t -> TCValues -> State h t
addLHTC s@(State {expr_env = eenv, type_env = tenv, curr_expr = cexpr, type_classes = tc}) tcv =
    let
        (eenv', eenvT) = addLHTCExprEnv eenv tenv tc tcv
        cexpr' = addLHTCCurrExpr eenv tenv cexpr tc tcv
    in
    replaceVarTy eenvT $ s { expr_env = eenv', curr_expr = cexpr' }

replaceVarTy :: ASTContainer m Expr => M.Map Name Type -> m -> m
replaceVarTy eenvT = modifyASTs (replaceVarTy' eenvT)

replaceVarTy' :: M.Map Name Type -> Expr -> Expr
replaceVarTy' eenvT v@(Var (Id n _))
    | Just t <- M.lookup n eenvT = Var (Id n t)
    | otherwise = v
replaceVarTy' _ e = e

-- | mergeLHSpecState
-- From the existing expression environement E, we  generate a new expression
-- environment E', with renamed copies of all expressions used in the LH
-- Specifications.
-- Then, we modify E by adding Assume/Asserts
-- based on the annotations.  However, these Assume/Asserts are only allowed to
-- reference expressions in E'.  This prevents infinite chains of Assumes/Asserts.  
-- Finally, the two expression environments are merged, before the whole state
-- is returned.
mergeLHSpecState :: [Maybe T.Text] -> [(Var, LocSpecType)] -> State h t -> ExprEnv -> TCValues -> State h t
mergeLHSpecState ns xs s@(State {expr_env = eenv, name_gen = ng, curr_expr = cexpr, known_values = knv }) meenv tcv =
    let
        -- ((meenv, mkv), ng') = doRenames (E.keys eenv) ng (eenv, knv)

        s' = addTrueAsserts ns $ mergeLHSpecState' (addAssertSpecType meenv tcv) xs s

        ng' = name_gen s'

        usedCexpr = filter (not . flip E.isSymbolic eenv) $ varNames cexpr
        eenvC = E.filterWithKey (\n _ -> n `elem` usedCexpr) eenv
        meenvC = E.filterWithKey (\n _ -> n `elem` usedCexpr) meenv
        ((usedCexpr', app_tys), ng'') = renameAll (usedCexpr, apply_types s') ng'

        usedZ = zip usedCexpr usedCexpr'

        cexpr' = foldr (uncurry rename) cexpr usedZ
        eenvC' = E.mapKeys (\n -> fromJust $ lookup n usedZ) eenvC
        meenvC' = E.mapKeys (\n -> fromJust $ lookup n usedZ) meenvC

        s'' = mergeLHSpecState' (addAssumeAssertSpecType meenv tcv) xs (s { expr_env = eenvC', name_gen = ng'' })
    in
    s'' { expr_env = E.union (E.union (E.union meenvC' meenv) (expr_env s')) $ expr_env s''
        , curr_expr = cexpr'
        , apply_types = app_tys }

-- | mergeLHSpecState'
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState' :: SpecTypeFunc h t -> [(Var, LocSpecType)] -> State h t -> State h t
mergeLHSpecState' _ [] s = s
mergeLHSpecState' f ((v,lst):xs) s =
    let
        (Id (Name n m _) _) = mkIdUnsafe v

        g2N = E.lookupNameMod n m (expr_env s)
    in
    case g2N of
        Just (n', e) ->
            mergeLHSpecState' f xs $ f n' e (val lst) s
        -- We hit a Nothing for certain functions we consider primitives but which
        -- LH has LT assumptions for. E.g. True, False...
        _ -> mergeLHSpecState' f xs s

-- addLHTCExprEnv
-- We add a LH type class dict for all polymorphic variables in all function
-- definitions.
addLHTCExprEnv :: ExprEnv -> TypeEnv -> TypeClasses -> TCValues -> (ExprEnv, M.Map Name Type)
addLHTCExprEnv eenv tenv tc tcv = 
    let
        lh = lhTC tcv

        eenv' = modifyLamTops (addLHTCLams lh) eenv
        eenvT = E.map' typeOf eenv'
        eenv'' = modifyContainedASTs (addLHTCCalls eenv tenv tc lh) eenv'
    in
    (eenv'', eenvT)

addLHTCCurrExpr :: ExprEnv -> TypeEnv -> CurrExpr -> TypeClasses -> TCValues -> CurrExpr
addLHTCCurrExpr eenv tenv cexpr tc tcv = 
    let
        lh = lhTC tcv

        cexpr' = modifyContainedASTs (addLHTCCalls eenv tenv tc lh) cexpr
    in
    cexpr'

modifyLamTops :: ASTContainer m Expr => (Expr -> Expr) -> m -> m
modifyLamTops f = modifyContainedASTs (modifyLamTops' f)

modifyLamTops' :: (Expr -> Expr) -> Expr -> Expr
modifyLamTops' f l@(Lam _ e) =
    let
        l' = f l
    in
    case l' of
        Lam i e' -> Lam i $ modifyAfterLams (modifyLamTops' f) e'
        e' -> modifyLamTops' f e
modifyLamTops' f e = modifyChildren (modifyLamTops' f) e

modifyAfterLams :: (Expr -> Expr) -> Expr -> Expr
modifyAfterLams f (Lam i e) = Lam i $ modifyAfterLams f e
modifyAfterLams f e = f e

-- | addLHTCLams
-- Adds lambdas to Expr to pass in the LH TC
addLHTCLams :: Name -> Expr -> Expr
addLHTCLams lh e =
    let
        tva = nub . mapMaybe (tYPEOrTyVar) $ args e
        
        ds = map (Name "d" Nothing) [1 .. length tva]

        as = map (\(d, i) -> (idName i, Lang.Id d $ TyConApp lh [TyVar i])) (zip ds tva)
    in
    if not (hasLHTC lh e) 
        -- then foldr Lam e $ map snd as
        then addLams lh e as 
        else e

addLams :: Name -> Expr -> [(Name, Lang.Id)] -> Expr
addLams _ e [] = e
addLams lh l@(Lam i@(Id n t) e) is =
    if isTYPE t 
        then
            let
                ts = getTypeNames l
                dictIds = mapMaybe (flip lookup is) ts
            in
            pastTYPE (addLHTCLams lh) $ foldr Lam l dictIds
        else Lam i $ addLams lh e is
addLams _ e _ = e

pastTYPE :: (Expr -> Expr) -> Expr -> Expr
pastTYPE f le@(Lam i@(Id n t) e) =
    if isTYPE t then Lam i $ pastTYPE f e else f le

getTypeNames :: Expr -> [Name]
getTypeNames (Lam (Id n t) e) = if isTYPE t then n:getTypeNames e else []
getTypeNames _ = []

tYPEOrTyVar :: Lang.Id -> Maybe Lang.Id
tYPEOrTyVar e
    | isTYPE $ typeOf e = Just e
    | (TyVar i@(Id _ TYPE)) <- typeOf e = Just i
    | otherwise = Nothing

hasLHTC :: Name -> Expr -> Bool
hasLHTC lh (Lam (Id _ (TyConApp n _)) e) = if n == lh then True else hasLHTC lh e 
hasLHTC lh (Lam _ e) = hasLHTC lh e 
hasLHTC _ _ = False

modifyAppTops :: (Expr -> Expr) -> Expr -> Expr
modifyAppTops f a@(App _ _) =
    let
        a' = f a
    in
    case a' of
        App e e' -> modifyAppRHS (modifyAppTops f) (App e e')
        e -> modifyAppTops f e
modifyAppTops f e = modifyChildren (modifyAppTops f) e

-- modifyAppRHS :: (Expr -> Expr) -> Expr -> Expr
-- modifyAppRHS f (App e e') = App e $ modifyAppTops f e'
-- modifyAppRHS f e = f e

-- | addLHTCCalls
-- Adds App's to function calls to pass the LH TC
addLHTCCalls :: ExprEnv -> TypeEnv -> TypeClasses -> Name -> Expr -> Expr
addLHTCCalls eenv tenv tc lh e =
    let
        lh_dicts = lhDicts lh e
    in
    modifyAppTops (addTCPasses eenv tenv tc lh_dicts lh) e
    -- let
    --     fc = nonDataFunctionCalls e
    --     lh_dicts = lhDicts lh e

    --     fc' = nubBy (\x y -> fst x == fst y) $ mapMaybe (addTCPasses (E.keys eenv) tenv tc lh_dicts lh) fc
    -- in
    -- foldr (uncurry replaceASTs) e fc'

lhDicts :: Name -> Expr -> [(Type, Lang.Id)]
lhDicts lh (Lam i@(Lang.Id _ (TyConApp n [t])) e) =
    if lh == n then (t, i):lhDicts lh e else lhDicts lh e
lhDicts _ _ = []

addTCPasses :: ExprEnv -> TypeEnv -> TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> Expr
addTCPasses eenv tenv tc ti lh e =
    let
        as = reverse $ passedArgs e
        e' = appCenter e

        e'' = addArgs tenv tc ti lh e' as 
    in
    case e' of
        Var _ -> e''
        Data _ -> e
        _ -> inAppCenter (addLHTCCalls eenv tenv tc lh) e'' --mkApp (addLHTCCalls eenv tenv tc lh e':as) -- Just (e', foldl' App e'' lht) else Nothing

inAppCenter :: (Expr -> Expr) -> Expr -> Expr
inAppCenter f (App e e') = App (inAppCenter f e) e'
inAppCenter f e = f e

addArgs :: TypeEnv -> TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> [Expr] -> Expr
addArgs _ _ _ _ e [] = e
addArgs tenv tc ti lh e as@(e':es)
    | isType e' =
        let
            (ts, as') = span isType as
        in
        addArgs tenv tc ti lh (mkApp (addLHDictArgs tenv tc ti lh e ts:ts)) as'
    | otherwise = addArgs tenv tc ti lh (App e e') es

isType :: Expr -> Bool
isType (Var (Id n t)) = isTYPE t
isType (Type _) = True
isType _ = False

addLHDictArgs :: TypeEnv -> TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> [Expr] -> Expr
addLHDictArgs tenv tc ti lh e (t@(Type _):ts) =
    case typeExprType tenv t of
        Just t' -> addLHDictArgs tenv tc ti lh (App e (typeToLHTypeClass tc ti lh t')) ts
        Nothing -> addLHDictArgs tenv tc ti lh e ts
addLHDictArgs tenv tc ti lh e ((Var i):ts) =
    addLHDictArgs tenv tc ti lh (App e (typeToLHTypeClass tc ti lh (TyVar i))) ts
addLHDictArgs _ _ _ _ e _ = e

-- addTCPasses :: [Name] -> TypeEnv -> TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> Maybe (Expr, Expr)
-- addTCPasses ens tenv tc ti lh e =
--     let
--         tva = mapMaybe (typeExprType tenv) $ reverse $ passedArgs e

--         lht = map (typeToLHTypeClass tc ti lh) tva

--         e' = appCenter e

--         -- Update the type of e
--         e'' = addToType (map typeOf lht) e'
--     in
--     if varInNames ens e' then Just (e', foldl' App e'' lht) else Nothing

varInNames :: Expr -> Bool
varInNames (Data _) = False
varInNames _ = True
-- varInNames ns (Var (Id n _)) = n `elem` ns
-- varInNames _ _ = False

typeExprType :: TypeEnv -> Expr -> Maybe Type
typeExprType tenv (Type t) =
    case t of
        TyConApp n ts ->
            case M.lookup n tenv of
                Just adt -> if length ts == length (bound_names adt) then Just t else Nothing
                Nothing -> Just t
        _ -> Just t
typeExprType _ _ = Nothing

addToType :: [Type] -> Expr -> Expr
addToType ts (Var (Id n t)) =
    let
        t' = foldr TyFun t ts
    in
    Var (Id n t')
addToType [] e = e
addToType _ _ = error $ "Non Var in addToType"

typeToLHTypeClass :: TypeClasses -> [(Type, Lang.Id)] -> Name -> Type -> Expr
typeToLHTypeClass tc ti lh t =
    case lookupTCDict tc lh t of
        Just lhD -> 
            case t of 
                TyConApp _ ts -> mkApp $ Var lhD:map (typeToLHTypeClass tc ti lh) ts ++ map (Type) ts
                _ -> Var lhD
        Nothing -> case lookup t ti of
            Just lhD -> Var lhD
            Nothing -> Var (Lang.Id (Name "BAD" Nothing 0) TyUnknown)-- TODO : Can hit this when have TyFun... -- error $ "Typeclass not found in typeToLHTypeClass" ++ show t

type SpecTypeFunc h t = Name -> Expr -> SpecType -> State h t -> State h t

addAssertSpecType :: ExprEnv -> TCValues -> SpecTypeFunc h t
addAssertSpecType meenv tcv n e st (s@State { expr_env = eenv
                                            , name_gen = ng }) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        st' = convertAssertSpecType tcv (s { expr_env = meenv }) st b' Nothing

        newE = 
            insertInLams 
                (\is e' ->
                    let 
                        fc = FuncCall {funcName = n, arguments = map Var is, returns = Var b}
                    in
                    Let [(b, e')] $ Lang.Assert (Just fc) (mkApp $ st':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng''}

addAssumeAssertSpecType :: ExprEnv -> TCValues -> SpecTypeFunc h t
addAssumeAssertSpecType meenv tcv n e st (s@State { expr_env = eenv
                                                  , name_gen = ng }) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        assumest' = convertAssumeSpecType tcv (s { expr_env = meenv }) st
        assertst' = convertAssertSpecType tcv (s { expr_env = meenv }) st b' Nothing

        newE =
            insertInLams 
                (\is e' -> 
                    let
                        fc = FuncCall {funcName = n, arguments = map Var is, returns = Var b}
                    in
                    Let [(b, e')] $ Lang.Assume (mkApp $ assumest':map Var is)
                                  $ Lang.Assert (Just fc) (mkApp $ assertst':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng''}

-- | addTrueAsserts
-- adds an assertion of True to all functions without an assertion
addTrueAsserts :: [Maybe T.Text] -> State h t -> State h t
addTrueAsserts mn s@(State {expr_env = eenv, type_env = tenv, name_gen = ng, known_values = kv, type_classes = tc}) =
    let
        (b, ng') = freshName ng
    in
    s {expr_env = E.mapWithKey (addTrueAsserts' mn kv tenv (map idName $ tcDicts tc) b) eenv, name_gen = ng'}

addTrueAsserts' :: [Maybe T.Text] -> KnownValues -> TypeEnv -> [Name] -> Name -> Name -> Expr -> Expr
addTrueAsserts' mn kv tenv tcn bn n@(Name nn _ _) e =
    let
        t = returnType e
        b = Id bn t
    
        ee = insertInLams 
                (\is e' ->
                    let
                        fc = FuncCall {funcName = n, arguments = map Var is, returns = Var b}
                    in
                    Let [(b, e')] $ Lang.Assert (Just fc) (mkTrue kv tenv) (Var b))
                e
    in
    if not (hasAssert e) && not (n `elem` tcn) && moduleName n `elem` mn then ee else e

moduleName :: Name -> Maybe T.Text
moduleName (Name _ m _) = m

hasAssert :: Expr -> Bool
hasAssert = getAny . eval hasAssert'

hasAssert' :: Expr -> Any
hasAssert' (Assert _ _ _) = Any True
hasAssert' _ = Any False

-- | convertSpecType
-- We create an Expr from a SpecType in two phases.  First, we create outer
-- lambda expressions, then we create a conjunction of m boolean expressions
-- describing allowed  values of the bound variables
convertAssertSpecType :: TCValues -> State h t -> SpecType -> Lang.Id -> Maybe (M.Map Name Type) -> Expr
convertAssertSpecType tcv s@(State { type_env = tenv }) st ret m =
    let
        nt = convertSpecTypeDict tcv s st

        ds = map (\(n, t) -> Id n t) nt
        dclams = foldr (.) id (map Lam ds) 

        lams = specTypeLams tenv st 
        lams' = dclams . lams . Lam ret

        m' = maybe (M.fromList nt) id m
        apps = specTypeApps st tcv s m' ret
    in
    primInject $ lams' apps

convertAssumeSpecType :: TCValues -> State h t -> SpecType -> Expr
convertAssumeSpecType tcv s@(State { type_env = tenv }) st =
    let
        nt = convertSpecTypeDict tcv s st

        ds = map (\(n, t) -> Id n t) nt
        dclams = foldr (.) id (map Lam ds) 

        lams = specTypeLams tenv st 
        lams' = dclams . lams

        apps = assumeSpecTypeApps st tcv s (M.fromList nt)
    in
    primInject $ lams' apps

convertSpecTypeDict :: TCValues -> State h t -> SpecType -> [(Name, Type)]
convertSpecTypeDict tcv (State {type_env = tenv}) st =
    let
        lh = lhTC tcv

        tva = nub . filter isTyVar $ specTypeLamTypes tenv st
        lhtc = map (\t -> TyConApp lh [t]) tva

        dsnames = map (Name "d" Nothing) [0 .. (length tva - 1)]
    in 
    zip dsnames lhtc

specTypeLams :: TypeEnv -> SpecType -> (Expr -> Expr)
specTypeLams _ (RVar {}) = id
specTypeLams tenv (RFun {rt_bind = b, rt_in = fin, rt_out = fout }) =
    let
        t = unsafeSpecTypeToType tenv fin
        i = convertSymbolT b t
    in
    Lam i . specTypeLams tenv fout
specTypeLams tenv (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) =
    let
        i = mkIdUnsafe v
    in
    Lam i . specTypeLams tenv rty
specTypeLams _ r@(RAllP {}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams _ r@(RAllS {}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams _ (RApp {}) = id
specTypeLams _ r = error ("Error in specTypeLams " ++ (show $ PPR.rtypeDoc Full r))

specTypeLamTypes :: TypeEnv -> SpecType -> [Type]
specTypeLamTypes _ (RVar {}) = []
specTypeLamTypes tenv (RFun {rt_bind = b, rt_in = fin, rt_out = fout}) =
    let
        t = unsafeSpecTypeToType tenv fin
        i = convertSymbolT b t
    in
    typeOf i:specTypeLamTypes tenv fout
specTypeLamTypes tenv (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) =
    let
        i = mkIdUnsafe v
    in
    (TyVar i):specTypeLamTypes tenv rty
specTypeLamTypes _ r@(RAllP {}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes _ r@(RAllS {}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes _ (RApp {}) = []
specTypeLamTypes _ r = error ("Error in specTypeLamTypes " ++ (show $ PPR.rtypeDoc Full r))

specTypeApps :: SpecType -> TCValues -> State h t -> M.Map Name Type -> Lang.Id -> Expr
specTypeApps st tcv s@(State {expr_env = eenv}) m b =
    let
        ste = specTypeApps' st tcv s m b
    in
    foldl1' (\e -> App (App (mkAnd eenv) e)) $ ste

assumeSpecTypeApps :: SpecType -> TCValues -> State h t -> M.Map Name Type -> Expr
assumeSpecTypeApps st tcv s@(State {expr_env = eenv, type_env = tenv, name_gen = ng, known_values = knv}) m =
    let
        (i, _) = freshId TyUnknown ng
    in
    case init $ specTypeApps' st tcv s m i of
        xs@(_:_) -> foldl1' (\e -> App (App (mkAnd eenv) e)) xs
        _ -> mkTrue knv tenv

specTypeApps' :: SpecType -> TCValues -> State h t -> M.Map Name Type -> Lang.Id -> [Expr]
specTypeApps' (RVar {rt_var = (RTV v), rt_reft = r}) tcv s m b =
    let
        symb = reftSymbol $ ur_reft r

        i = mkIdUnsafe v

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert (idName symbId) (TyVar i) m 

        re =  convertLHExpr (reftExpr $ ur_reft r) Nothing tcv s m'
    in
    [App (Lam symbId re) (Var b)]
specTypeApps' (RFun {rt_bind = rb, rt_in = fin, rt_out = fout }) tcv s@(State { type_env = tenv }) m b =
    -- TODO : rt_reft
    let
        t = unsafeSpecTypeToType tenv fin
        i = convertSymbolT rb t

        m' = M.insert (idName i) t m
    in
    case hasFuncType i of
        True -> specTypeApps' fout tcv s m b
        _ -> specTypeApps' fin tcv s m' i ++ specTypeApps' fout tcv s m' b
specTypeApps' (RAllT {rt_ty = rty}) tcv s m b =
    specTypeApps' rty tcv s m b
specTypeApps' (RApp {rt_tycon = c, rt_reft = r, rt_args = as}) tcv s@(State {expr_env = eenv, type_env = tenv, type_classes = tc}) m b =
    let
        symb = reftSymbol $ ur_reft r
        ty = case rTyConType tenv c as of
            Just ty' -> ty'
            Nothing -> error "Error in specTypeApps'"
        i = convertSymbolT symb ty

        argsPred = polyPredFunc as eenv tenv tc ty tcv s m b

        m' = M.insert (idName i) ty m

        re = convertLHExpr (reftExpr $ ur_reft r) Nothing tcv s m'

        an = mkAnd eenv
    in
    [App (App an (App (Lam i re) (Var b))) argsPred]

polyPredFunc :: [SpecType] -> ExprEnv -> TypeEnv -> TypeClasses -> Type -> TCValues -> State h t -> M.Map Name Type -> Lang.Id -> Expr
polyPredFunc as eenv tenv tc ty tcv s m b =
    let
        dict = fromJustErr "No lhDict for polyPredFunc" $ lhTCDict eenv tcv tc ty m
        as' = map (\a -> polyPredLam a tcv s m) as
    in
    mkApp $ [Var $ Id (lhPP tcv) TyUnknown, dict, Type (typeOf b)] ++ as' ++ [Var b]
    -- let
    --     ts = map (unsafeSpecTypeToType tenv) as
    --     ts' = map Type ts

    --     as' = map (\a -> polyPredLam a tcv s m) as

    --     typE = Type ty
    --     lhD = fromJustErr "No lhDict for polyPredFunc" $ lhTCDictNoArgs eenv tcv tc ty m

    --     lhDs = map (\t' -> fromJustErr "No lhDict for polyPredFuncArg" $ lhTCDictNoArgs eenv tcv tc t' m) ts
    -- in
    -- mkApp $ [Var $ Id (lhPP tcv) TyUnknown, lhD, typE] ++ lhDs ++ ts' ++ as' ++ [Var b]


polyPredLam :: SpecType -> TCValues -> State h t -> M.Map Name Type -> Expr
polyPredLam rapp tcv s@(State {type_env = tenv, name_gen = ng}) m =
    let
        t = unsafeSpecTypeToType tenv rapp

        (i, _) = freshId t ng
    in
    convertAssertSpecType tcv s rapp i (Just m)

replaceLam :: Lang.Id -> Expr -> Expr -> Expr
replaceLam i true = modify (replaceLam' i true)

replaceLam' :: Lang.Id -> Expr -> Expr -> Expr
replaceLam' i true l@(App (Lam _ _) (Var i')) = if i == i' then true else l
replaceLam' _ _ e = e

unsafeSpecTypeToType :: TypeEnv -> SpecType -> Type
unsafeSpecTypeToType tenv st =
    case specTypeToType tenv st of
        Just t -> t
        Nothing -> error $ "Error in unsafeSpecTypeToType " ++ show (pprint $ st)

specTypeToType :: TypeEnv -> SpecType -> Maybe Type
specTypeToType _ (RVar {rt_var = (RTV v)}) =
    let
        i = mkIdUnsafe v
    in
    Just $ TyVar i
specTypeToType tenv (RFun {rt_in = fin, rt_out = fout}) =
    let
        t = specTypeToType tenv fin
        t2 = specTypeToType tenv fout
    in
    case (t, t2) of
        (Just t', Just t2') -> Just $ TyFun t' t2'
        _ -> Nothing
specTypeToType tenv (RAllT {rt_tvbind = RTVar (RTV v) _, rt_ty = rty}) =
    let
        i = mkIdUnsafe v
    in
    fmap (TyForAll (NamedTyBndr i)) $ specTypeToType tenv rty
specTypeToType tenv (RApp {rt_tycon = c, rt_args = as}) = rTyConType tenv c as
specTypeToType _ rty = error $ "Unmatched pattern in specTypeToType " ++ show (pprint rty)

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

rTyConType :: TypeEnv -> RTyCon -> [SpecType]-> Maybe Type
rTyConType tenv rtc sts = 
    let
        n = nameModMatch (mkTyConName HM.empty . rtc_tc $ rtc) tenv

        ts = map (specTypeToType tenv) sts
    in
    case (not . any isNothing $ ts) of
        True -> fmap (\n' -> TyConApp n' (catMaybes ts)) n
        False -> Nothing

rtvInfoSymbol :: RTVInfo a -> Symbol
rtvInfoSymbol (RTVInfo {rtv_name = s}) = s

convertLHExpr :: Ref.Expr -> Maybe Type -> TCValues -> State h t -> M.Map Name Type -> Expr
convertLHExpr (ESym (SL n)) _ _ _ _ = Var $ Id (Name n Nothing 0) TyUnknown
convertLHExpr (ECon c)  t _ (State {known_values = knv, type_env = tenv}) _ = convertCon t knv tenv c
convertLHExpr (EVar s) t _ (State { expr_env = eenv, type_env = tenv }) m = convertEVar (symbolName s) eenv tenv m
convertLHExpr (EApp e e') _ tcv s@(State {type_classes = tc}) m =
    let
        f = convertLHExpr e Nothing tcv s m
        f_ar_t@(~(TyConApp _ f_ar_ts)) = last $ argumentTypes f
    in
    case convertLHExpr e' (Just f_ar_t) tcv s m of
        v@(Var (Id n (TyConApp tn ts))) -> 
            let -- trace ("t args = " ++ show (argumentTypes f) ++ "\nts = " ++ show ts ++ "\n") 
                -- te = map Type $ nub $ filter isTyVar $ argumentTypes f-- map Type ts-- nub $ map (Type) $ concatMap tyVars ts --TODO : Is this right?  Only 1 non-Type arg to a measure, and should have type args in order?
                specTo = concatMap (map snd) $ map M.toList $ map (snd . uncurry (specializes M.empty)) $ zip ts f_ar_ts
                te = map Type specTo-- trace ("m = " ++ show specTo ++ "\nts = " ++ show ts ++ "\nf_ar_ts = " ++ show (f_ar_ts)) nub $ map (Type) $ concatMap tyVars ts

                lh = lhTC tcv
                ti = typeIdList tcv m
                tcs = map (typeToLHTypeClass tc ti lh) ts

                fw = mkApp $ f:tcs

                apps = mkApp $ fw:te ++ [v]
            in
            apps
        e'' -> App f e''
convertLHExpr (ENeg e) t tcv s@(State { expr_env = eenv, type_classes = tc, known_values = knv }) m =
    let
        e' = convertLHExpr e t tcv s m

        t' = typeOf e'

        ndict = fromJustErr "No lnumDict for ENeg" $ numDict eenv knv tc t' m

        lhdict = fromJustErr "No lhDict for ENeg" $ lhTCDict eenv tcv tc t' m
    in
    mkApp [ mkPrim Negate eenv
          , lhdict
          , Type t'
          , ndict
          , e']
convertLHExpr (EBin b e e') pt tcv s@(State { expr_env = eenv, type_classes = tc, known_values = knv }) m =
    let
        lhe = convertLHExpr e pt tcv s m
        lhe' = convertLHExpr e' pt tcv s m

        -- t = typeOf lhe
        t = typeOf lhe
        t' = typeOf lhe'

        (lhe2, lhe2') = if t == t' then (Just lhe, Just lhe') 
                          else (callFromInteger eenv knv tcv tc lhe t' m, callFromInteger eenv knv tcv tc lhe' t m)

        lhe3 = maybe lhe id lhe2
        lhe3' = maybe lhe' id lhe2'

        t2 = favorNonTyInteger knv t t'

        ndict = fromJustErr ("No numDict for EBin\n" ++ show lhe ++ "\n" ++ show lhe' ++ "\n" ++ show t ++ "\n" ++ show t') $ bopDict b eenv knv tc t2 m

        lhdict = fromJustErr "No lhDict for EBin" $ lhTCDict eenv tcv tc t2 m
    in
    mkApp [ convertBop b eenv
          , lhdict
          , Type t2
          , ndict
          , lhe3
          , lhe3']
convertLHExpr (EIte b e1 e2) t tcv s@(State { type_env = tenv, name_gen = ng, known_values = knv }) m =
    let
        tr = mkDCTrue knv tenv
        fs = mkDCFalse knv tenv
        boolT = Lang.tyBool knv

        (cb, ng2) = freshId boolT ng
        s' = s {name_gen = ng2}

        bE = convertLHExpr b Nothing tcv s' m
        e1' = convertLHExpr e1 t tcv s' m
        e2' = convertLHExpr e2 t tcv s' m

        a1 = Lang.Alt (DataAlt tr []) e1'
        a2 = Lang.Alt (DataAlt fs []) e2'
    in
    Case bE cb [a1, a2]
convertLHExpr (PAnd es) _ tcv s@(State { known_values = knv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e Nothing tcv s m) es of
        [] -> mkTrue knv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkAnd eenv) e)) (mkTrue knv tenv) es'
convertLHExpr (POr es) _ tcv s@(State { known_values = knv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e Nothing tcv s m) es of
        [] -> mkFalse knv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkOr eenv) e)) (mkFalse knv tenv) es'
convertLHExpr (PNot e) _ tcv s@(State {expr_env = eenv }) m =
    App (mkNot eenv) $ convertLHExpr e Nothing tcv s m
convertLHExpr (PImp e e') _ tcv s@(State { expr_env = eenv }) m =
    mkApp [mkImplies eenv, convertLHExpr e Nothing tcv s m, convertLHExpr e' Nothing tcv s m]
convertLHExpr (PIff e e') _ tcv s@(State { expr_env = eenv }) m =
    mkApp [mkIff eenv, convertLHExpr e Nothing tcv s m, convertLHExpr e' Nothing tcv s m]
convertLHExpr (PAtom brel e e') pt tcv s@(State {expr_env = eenv, known_values = knv, type_classes = tc}) m =
    let
        brel' = convertBrel brel tcv

        ec = convertLHExpr e pt tcv s m
        ec' = convertLHExpr e' pt tcv s m

        t = returnType ec
        t' = returnType ec'

        -- (ec2, ec2', t2) = (ec, ec', t)
        (ec2, ec2') = if t == t' then (Just ec, Just ec') 
                          else (callFromInteger eenv knv tcv tc ec t' m, callFromInteger eenv knv tcv tc ec' t m)

        ec3 = maybe ec id ec2
        ec3' = maybe ec' id ec2'

        t2 = favorNonTyInteger knv t t'

        dict = fromJustErr ("No lhDict for PAtom ec = " ++ show ec ++ "\nec' = " 
                            ++ show ec' ++ "\nt2 = " ++ show t2 ++ "\nm = " ++ show m) $ lhTCDict eenv tcv tc t2 m

        app = mkApp [brel', dict, Type t2, ec3, ec3']
    in
    mkApp [brel', dict, Type t2, ec3, ec3']
convertLHExpr e _ _ _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

convertSymbol :: Name -> ExprEnv -> M.Map Name Type -> Lang.Id
convertSymbol nm@(Name n md _) eenv m =
    let
        t = maybe TyUnknown id $ M.lookup nm m
    in
    case E.lookupNameMod n md eenv of
        Just (n', e) -> Id n' (typeOf e)
        _ -> Id nm t

convertEVar :: Name -> ExprEnv -> TypeEnv -> M.Map Name Type -> Lang.Expr
convertEVar nm@(Name n md _) eenv tenv m =
    let
        t = maybe TyUnknown id $ M.lookup nm m
    in
    case (E.lookupNameMod n md eenv, getDataConNameMod' tenv nm) of
        (Just (n', e), _) -> Var $ Id n' (typeOf e)
        (_, Just dc) -> Data dc 
        _ -> Var $ Id nm t

convertSymbolT :: Symbol -> Type -> Lang.Id
convertSymbolT s = Id (symbolName s)

-- If possible, we split symbols at the last "." not in parenthesis, to
-- correctly set module names 
symbolName :: Symbol -> Name
symbolName s =
    let
        t = symbolSafeText s
        l = T.last t

        ((m, n), i) =
            case l of
                ')' -> (T.breakOnEnd ".(" t, 2)
                _ -> (T.breakOnEnd "." t, 1)

        m' = T.dropEnd i m
    in
    case (m', n) of
        (n', "") -> Name n' Nothing 0
        _ -> Name n (Just m') 0

convertCon :: Maybe Type -> KnownValues -> TypeEnv -> Constant -> Expr
convertCon (Just (TyConApp n _)) knv tenv (Ref.I i)
    | n == KV.tyInt knv = App (mkDCInt knv tenv) (Lit . LitInt $ fromIntegral i)
convertCon _ knv tenv (Ref.I i) = App (mkDCInteger knv tenv) (Lit . LitInt $ fromIntegral i)
convertCon _ knv tenv (Ref.R d) = App (mkDCDouble knv tenv) (Lit . LitDouble $ toRational d)

convertBop :: Bop -> ExprEnv -> Expr
convertBop Ref.Plus = mkPlus
convertBop Ref.Minus = mkMinus
convertBop Ref.Times = mkMult
convertBop Ref.Div = mkDiv
convertBop Ref.Mod = mkMod
convertBop Ref.RTimes = mkMult
convertBop Ref.RDiv = mkDiv

bopDict :: Bop -> ExprEnv -> KnownValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
bopDict Ref.Mod = integralDict
bopDict Ref.Mod = integralDict
bopDict _ = numDict

lhTCDict :: ExprEnv -> TCValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
lhTCDict eenv tcv tc t m =
    case fmap Var $ lookupTCDict tc (lhTC tcv) t of
        Just d -> case t of 
                TyConApp _ ts -> Just $ mkApp $ d:mapMaybe (\t' -> lhTCDict eenv tcv tc t' m) ts ++ map (Type) ts -- ++ m
                _ -> Just d 
        Nothing -> 
            case find (tyVarInTyAppHasName (lhTC tcv) . snd) (M.toList m) of
                Just (s, _) -> Just . Var $ convertSymbol s eenv m
                Nothing -> Nothing

lhTCDictNoArgs :: ExprEnv -> TCValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
lhTCDictNoArgs eenv tcv tc t m =
    case fmap Var $ lookupTCDict tc (lhTC tcv) t of
        Just d -> Just d
        Nothing -> 
            case find (tyVarInTyAppHasName (lhTC tcv) . snd) (M.toList m) of
                Just (s, _) -> Just . Var $ convertSymbol s eenv m
                Nothing -> Nothing



numDict :: ExprEnv -> KnownValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
numDict eenv knv tc t m =
    case numTCDict knv tc t of
        Just d -> Just . Var $ d
        Nothing ->
            case find (tyVarInTyAppHasName (numTC knv) . snd) (M.toList m) of
                Just (s, _) -> Just . Var $ convertSymbol s eenv m
                Nothing -> Nothing

integralDict :: ExprEnv -> KnownValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
integralDict eenv knv tc t m =
    case integralTCDict knv tc t of
        Just d -> Just . Var $ d
        Nothing ->
            case find (tyVarInTyAppHasName (numTC knv) . snd) (M.toList m) of
                Just (s, _) -> Just . Var $ convertSymbol s eenv m
                Nothing -> Nothing

callFromInteger :: ExprEnv -> KnownValues -> TCValues -> TypeClasses ->  Expr -> Type -> M.Map Name Type -> Maybe Expr
callFromInteger eenv knv tcv tc e t m =
    let
        retT = returnType e

        lhdict = lhTCDict eenv tcv tc t m
        ndict = numDict eenv knv tc t m

        fIntgr = mkFromInteger eenv
    in
    if retT /= Lang.tyInteger knv then
        Just e
    else
        case (lhdict, ndict) of
            (Just lhdict', Just ndict') -> 
                Just $ mkApp [ fIntgr
                             , lhdict'
                             , Type t
                             , ndict'
                             , e]
            _ -> Nothing

favorNonTyInteger :: KnownValues -> Type -> Type -> Type
favorNonTyInteger knv t t' =
    if t /= Lang.tyInteger knv then
        t
    else
        t'

fromJustErr :: String -> Maybe a -> a
fromJustErr _ (Just x) = x
fromJustErr s _ = error s

-- lhTCDict :: TCValues -> TypeClasses -> Type -> Maybe Expr
-- lhTCDict tcv tc = fmap Var . lookupTCDict tc (lhTC tcv)

convertBrel :: Brel -> TCValues -> Expr
convertBrel Ref.Eq tcv = Var $ Id (lhEq tcv) TyUnknown
convertBrel Ref.Ne tcv = Var $ Id (lhNe tcv) TyUnknown
convertBrel Ref.Gt tcv = Var $ Id (lhGt tcv) TyUnknown
convertBrel Ref.Ge tcv = Var $ Id (lhGe tcv) TyUnknown
convertBrel Ref.Lt tcv = Var $ Id (lhLt tcv) TyUnknown
convertBrel Ref.Le tcv = Var $ Id (lhLe tcv) TyUnknown


tyVarInTyAppHasName :: Name -> Type -> Bool
tyVarInTyAppHasName n (TyConApp n' (TyVar (Id _ _):_)) = n == n'
tyVarInTyAppHasName _ _ = False

typeIdList :: TCValues -> M.Map Name Type -> [(Type, Lang.Id)]
typeIdList tcv =
    map (\(n, t) -> (head $ tyConAppList t, Id n t)) . M.toList . M.filter (tyVarInTyAppHasName (lhTC tcv))

tyConAppList :: Type -> [Type]
tyConAppList (TyConApp _ ts) = ts
tyConAppList _ = []
