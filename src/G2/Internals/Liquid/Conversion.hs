{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion ( addLHTC
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

addLHTC :: State h t -> TCValues -> State h t
addLHTC s@(State {expr_env = eenv, curr_expr = cexpr, type_classes = tc}) tcv =
    let
        eenv' = addLHTCExprEnv eenv tc tcv
        cexpr' = addLHTCCurrExpr cexpr tc tcv
    in
    s { expr_env = eenv', curr_expr = cexpr' }

-- | mergeLHSpecState
-- From the existing expression environement E, we  generate a new expression
-- environment E', with renamed copies of all expressions used in the LH
-- Specifications.
-- Then, we modify E by adding Assume/Asserts
-- based on the annotations.  However, these Assume/Asserts are only allowed to
-- reference expressions in E'.  This prevents infinite chains of Assumes/Asserts.  
-- Finally, the two expression environments are merged, before the whole state
-- is returned.
mergeLHSpecState :: [Maybe T.Text] -> [(Var, LocSpecType)] -> State h t -> TCValues -> (State h t, KnownValues)
mergeLHSpecState ns xs s@(State {expr_env = eenv, name_gen = ng, curr_expr = cexpr, known_values = knv }) tcv =
    let
        ((meenv, mkv), ng') = doRenames (E.keys eenv) ng (eenv, knv)

        s' = addTrueAsserts ns $ mergeLHSpecState' (addAssertSpecType meenv tcv) xs (s { name_gen = ng' })

        usedCexpr = filter (not . flip E.isSymbolic eenv) $ varNames cexpr
        eenvC = E.filterWithKey (\n _ -> n `elem` usedCexpr) eenv
        (usedCexpr', ng'') = renameAll usedCexpr ng'

        usedZ = zip usedCexpr usedCexpr'

        cexpr' = foldr (uncurry rename) cexpr usedZ
        eenvC' = E.mapKeys (\n -> fromJust $ lookup n usedZ) eenvC

        s'' = mergeLHSpecState' (addAssumeAssertSpecType meenv tcv) xs (s { expr_env = eenvC', name_gen = ng'' })
    in
    (s'' { expr_env = E.union (E.union meenv (expr_env s')) $ expr_env s''
         , curr_expr = cexpr' }
    , mkv )

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
addLHTCExprEnv :: ExprEnv -> TypeClasses -> TCValues -> ExprEnv
addLHTCExprEnv eenv tc tcv = 
    let
        lh = lhTC tcv

        eenv' = modifyContainedASTs (addLHTCLams lh) eenv
        eenv'' = modifyContainedASTs (addLHTCCalls tc lh) eenv'
    in
    eenv''

addLHTCCurrExpr :: CurrExpr -> TypeClasses -> TCValues -> CurrExpr
addLHTCCurrExpr cexpr tc tcv = 
    let
        lh = lhTC tcv

        cexpr' = modifyContainedASTs (addLHTCCalls tc lh) cexpr
    in
    cexpr'

-- | addLHTCLams
-- Adds lambdas to Expr to pass in the LH TC
addLHTCLams :: Name -> Expr -> Expr
addLHTCLams lh e =
    let
        tva = nub . mapMaybe (tYPEOrTyVar) $ args e
        
        ds = map (Name "d" Nothing) [1 .. length tva]

        as = map (\(d, i) -> Lang.Id d $ TyConApp lh [TyVar i]) (zip ds tva)
    in
    if not (hasLHTC lh e) then foldr Lam e as else e

tYPEOrTyVar :: Lang.Id -> Maybe Lang.Id
tYPEOrTyVar e
    | isTYPE $ typeOf e = Just e
    | (TyVar i@(Id _ TYPE)) <- typeOf e = Just i
    | otherwise = Nothing

hasLHTC :: Name -> Expr -> Bool
hasLHTC lh (Lam (Id _ (TyConApp n _)) e) = if n == lh then True else hasLHTC lh e 
hasLHTC lh (Lam _ e) = hasLHTC lh e 
hasLHTC _ _ = False

-- | addLHTCCalls
-- Adds App's to function calls to pass the LH TC
addLHTCCalls :: TypeClasses -> Name -> Expr -> Expr
addLHTCCalls tc lh e =
    let
        fc = nonDataFunctionCalls e
        lh_dicts = lhDicts lh e

        fc' = nubBy (\x y -> fst x == fst y) $ map (addTCPasses tc lh_dicts lh) fc
    in
    foldr (uncurry replaceASTs) e fc'

lhDicts :: Name -> Expr -> [(Type, Lang.Id)]
lhDicts lh (Lam i@(Lang.Id _ (TyConApp n [t])) e) =
    if lh == n then (t, i):lhDicts lh e else lhDicts lh e
lhDicts _ _ = []

addTCPasses :: TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> (Expr, Expr)
addTCPasses tc ti lh e =
    let
        tva = mapMaybe typeExprType $ passedArgs e

        lht = map (typeToLHTypeClass tc ti lh) tva

        e' = appCenter e

        -- Update the type of e
        e'' = addToType (map typeOf lht) e'
    in
    (e', foldl' App e'' lht)

appCenter :: Expr -> Expr
appCenter (App e _) = appCenter e
appCenter e = e

typeExprType :: Expr -> Maybe Type
typeExprType (Type t) = Just t
typeExprType _ = Nothing

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
        Just lhD -> Var lhD
        Nothing -> case lookup t ti of
            Just lhD -> Var lhD
            Nothing -> Var (Lang.Id (Name "BAD" Nothing 0) TyBottom)-- TODO : Can hit this when have TyFun... -- error $ "Typeclass not found in typeToLHTypeClass" ++ show t

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
        (i, _) = freshId TyBottom ng
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

        re =  convertLHExpr (reftExpr $ ur_reft r) tcv s m'
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

        re = convertLHExpr (reftExpr $ ur_reft r) tcv s m'

        an = mkAnd eenv
    in
    [App (App an (App (Lam i re) (Var b))) argsPred]

polyPredFunc :: [SpecType] -> ExprEnv -> TypeEnv -> TypeClasses -> Type -> TCValues -> State h t -> M.Map Name Type -> Lang.Id -> Expr
polyPredFunc as eenv tenv tc ty tcv s m b =
    let
        ts = map (unsafeSpecTypeToType tenv) as
        ts' = map Type ts

        as' = map (\a -> polyPredLam a tcv s m) as

        typE = Type ty
        lhD = fromJustErr "No lhDict for polyPredFunc" $ lhTCDict eenv tcv tc ty m

        lhDs = map (\t' -> fromJustErr "No lhDict for polyPredFuncArg" $ lhTCDict eenv tcv tc t' m) ts
    in
    mkApp $ [Var $ Id (lhPP tcv) TyBottom, lhD, typE] ++ lhDs ++ ts' ++ as' ++ [Var b]


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

convertLHExpr :: Ref.Expr -> TCValues -> State h t -> M.Map Name Type -> Expr
convertLHExpr (ESym (SL t)) _ _ _ = Var $ Id (Name t Nothing 0) TyBottom
convertLHExpr (ECon c) _ (State {known_values = knv, type_env = tenv}) _ = convertCon knv tenv c
convertLHExpr (EVar s) _ (State { expr_env = eenv, type_env = tenv }) m = convertEVar (symbolName s) eenv tenv m
convertLHExpr (EApp e e') tcv s@(State {type_classes = tc}) m =
    let
        f = convertLHExpr e tcv s m
    in
    case convertLHExpr e' tcv s m of
        v@(Var (Id _ (TyConApp _ ts))) -> 
            let
                te = map Type ts

                lh = lhTC tcv
                ti = typeIdList tcv m
                tcs = map (typeToLHTypeClass tc ti lh) ts

                fw = mkApp $ f:tcs

                apps = mkApp $ fw:te ++ [v]
            in
            apps
        e'' -> App f e''
convertLHExpr (ENeg e) tcv s@(State { expr_env = eenv, type_classes = tc, known_values = knv }) m =
    let
        e' = convertLHExpr e tcv s m

        t = typeOf e'

        ndict = fromJustErr "No lnumDict for ENeg" $ numDict eenv knv tc t m

        lhdict = fromJustErr "No lhDict for ENeg" $ lhTCDict eenv tcv tc t m
    in
    mkApp [ mkPrim Negate eenv
          , lhdict
          , Type t
          , ndict
          , e']
convertLHExpr (EBin b e e') tcv s@(State { expr_env = eenv, type_classes = tc, known_values = knv }) m =
    let
        lhe = convertLHExpr e tcv s m
        lhe' = convertLHExpr e' tcv s m

        -- t = typeOf lhe
        t = typeOf lhe
        t' = typeOf lhe'

        (lhe2, lhe2') = if t == t' then (lhe, lhe') 
                          else (callFromInteger eenv knv tcv tc lhe t' m, callFromInteger eenv knv tcv tc lhe' t m)

        t2 = favorNonTyInteger knv t t'

        ndict = fromJustErr ("No numDict for EBin\n" ++ show lhe ++ "\n" ++ show lhe' ++ "\n" ++ show t ++ "\n" ++ show t') $ bopDict b eenv knv tc t2 m

        lhdict = fromJustErr "No lhDict for EBin" $ lhTCDict eenv tcv tc t2 m

        app = mkApp [ convertBop b eenv
          , lhdict
          , Type t2
          , ndict
          , lhe2
          , lhe2']
    in
    mkApp [ convertBop b eenv
          , lhdict
          , Type t2
          , ndict
          , lhe2
          , lhe2']
convertLHExpr (EIte b e1 e2) tcv s@(State { type_env = tenv, name_gen = ng, known_values = knv }) m =
    let
        tr = mkDCTrue knv tenv
        fs = mkDCFalse knv tenv
        boolT = Lang.tyBool knv

        (cb, ng2) = freshId boolT ng
        s' = s {name_gen = ng2}

        bE = convertLHExpr b tcv s' m
        e1' = convertLHExpr e1 tcv s' m
        e2' = convertLHExpr e2 tcv s' m

        a1 = Lang.Alt (DataAlt tr []) e1'
        a2 = Lang.Alt (DataAlt fs []) e2'
    in
    Case bE cb [a1, a2]
convertLHExpr (PAnd es) tcv s@(State { known_values = knv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e tcv s m) es of
        [] -> mkTrue knv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkAnd eenv) e)) (mkTrue knv tenv) es'
convertLHExpr (POr es) tcv s@(State { known_values = knv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e tcv s m) es of
        [] -> mkFalse knv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkOr eenv) e)) (mkFalse knv tenv) es'
convertLHExpr (PNot e) tcv s@(State {expr_env = eenv }) m =
    App (mkNot eenv) $ convertLHExpr e tcv s m
convertLHExpr (PImp e e') tcv s@(State { expr_env = eenv }) m =
    mkApp [mkImplies eenv, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
convertLHExpr (PIff e e') tcv s@(State { expr_env = eenv }) m =
    mkApp [mkIff eenv, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
convertLHExpr (PAtom brel e e') tcv s@(State {expr_env = eenv, known_values = knv, type_classes = tc}) m =
    let
        brel' = convertBrel brel tcv

        ec = convertLHExpr e tcv s m
        ec' = convertLHExpr e' tcv s m

        t = returnType ec
        t' = returnType ec'

        -- (ec2, ec2', t2) = (ec, ec', t)
        (ec2, ec2') = if t == t' then (ec, ec') 
                          else (callFromInteger eenv knv tcv tc ec t' m, callFromInteger eenv knv tcv tc ec' t m)

        t2 = favorNonTyInteger knv t t'

        dict = fromJustErr ("No lhDict for PAtom ec = " ++ show ec ++ "\nec' = " 
                            ++ show ec' ++ "\nt2 = " ++ show t2 ++ "\nm = " ++ show m) $ lhTCDict eenv tcv tc t2 m

        app = mkApp [brel', dict, Type t2, ec2, ec2']
    in
    mkApp [brel', dict, Type t2, ec2, ec2']
convertLHExpr e _ _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

convertSymbol :: Name -> ExprEnv -> M.Map Name Type -> Lang.Id
convertSymbol nm@(Name n md _) eenv m =
    let
        t = maybe TyBottom id $ M.lookup nm m
    in
    case E.lookupNameMod n md eenv of
        Just (n', e) -> Id n' (typeOf e)
        _ -> Id nm t

convertEVar :: Name -> ExprEnv -> TypeEnv -> M.Map Name Type -> Lang.Expr
convertEVar nm@(Name n md _) eenv tenv m =
    let
        t = maybe TyBottom id $ M.lookup nm m
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

convertCon :: KnownValues -> TypeEnv -> Constant -> Expr
convertCon knv tenv (Ref.I i) = App (mkDCInteger knv tenv) (Lit . LitInt $ fromIntegral i)
convertCon knv tenv (Ref.R d) = App (mkDCDouble knv tenv) (Lit . LitDouble $ toRational d)

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
bopDict _ = numDict

lhTCDict :: ExprEnv -> TCValues -> TypeClasses -> Type -> M.Map Name Type -> Maybe Expr
lhTCDict eenv tcv tc t m =
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

callFromInteger :: ExprEnv -> KnownValues -> TCValues -> TypeClasses ->  Expr -> Type -> M.Map Name Type -> Expr
callFromInteger eenv knv tcv tc e t m =
    let
        retT = returnType e

        lhdict = fromJustErr "No lhDict for callFromInteger" $ lhTCDict eenv tcv tc t m
        ndict = fromJustErr "No numDict for callFromInteger" $ numDict eenv knv tc t m

        fIntgr = mkFromInteger eenv
    in
    if retT /= Lang.tyInteger knv then
        e
    else
        mkApp [ fIntgr
              , lhdict
              , Type t
              , ndict
              , e]

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
convertBrel Ref.Eq tcv = Var $ Id (lhEq tcv) TyBottom
convertBrel Ref.Ne tcv = Var $ Id (lhNe tcv) TyBottom
convertBrel Ref.Gt tcv = Var $ Id (lhGt tcv) TyBottom
convertBrel Ref.Ge tcv = Var $ Id (lhGe tcv) TyBottom
convertBrel Ref.Lt tcv = Var $ Id (lhLt tcv) TyBottom
convertBrel Ref.Le tcv = Var $ Id (lhLe tcv) TyBottom


tyVarInTyAppHasName :: Name -> Type -> Bool
tyVarInTyAppHasName n (TyConApp n' (TyVar (Id _ _):_)) = n == n'
tyVarInTyAppHasName _ _ = False

typeIdList :: TCValues -> M.Map Name Type -> [(Type, Lang.Id)]
typeIdList tcv =
    map (\(n, t) -> (head $ tyConAppList t, Id n t)) . M.toList . M.filter (tyVarInTyAppHasName (lhTC tcv))

tyConAppList :: Type -> [Type]
tyConAppList (TyConApp _ ts) = ts
tyConAppList _ = []
