{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion ( addLHTC
                                      , mergeLHSpecState) where

import G2.Internals.Translation
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.KnownValues
import G2.Internals.Liquid.Primitives
import G2.Internals.Liquid.TCValues

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import  Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref

import TyCon
import Var hiding (tyVarName, isTyVar)

import Data.Coerce
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import qualified Data.Text as T

import Debug.Trace

addLHTC :: State -> TCValues -> State
addLHTC s@(State {expr_env = eenv, curr_expr = cexpr, name_gen = ng, type_classes = tc}) tcv =
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
mergeLHSpecState :: [(Var, LocSpecType)] -> State -> TCValues -> State
mergeLHSpecState xs s@(State {expr_env = eenv, name_gen = ng, curr_expr = cexpr }) tcv =
    let
        (meenv, ng') = doRenames (E.keys eenv) ng eenv

        s' = mergeLHSpecState' (addAssertSpecType (mkAnd eenv) meenv tcv) xs (s { name_gen = ng' })

        usedCexpr = filter (not . flip E.isSymbolic eenv) $ varNames cexpr
        eenvC = E.filterWithKey (\n _ -> n `elem` usedCexpr) eenv
        (usedCexpr', ng'') = renameAll usedCexpr ng'

        usedZ = zip usedCexpr usedCexpr'

        cexpr' = foldr (uncurry rename) cexpr usedZ
        eenvC' = E.mapKeys (\n -> fromJust $ lookup n usedZ) eenvC

        s'' = mergeLHSpecState' (addAssumeAssertSpecType (mkAnd eenv) meenv tcv) xs (s { expr_env = eenvC', name_gen = ng'' })
    in
    s'' { expr_env = E.union (E.union meenv (expr_env s')) $ expr_env s''
        , curr_expr = cexpr' }

-- | mergeLHSpecState'
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState' :: SpecTypeFunc -> [(Var, LocSpecType)] -> State -> State
mergeLHSpecState' _ [] s = s
mergeLHSpecState' f ((v,lst):xs) s =
    let
        (Id (Name n m _) _) = mkId v

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
        tva = nub . filter (isTYPE . typeOf) $ args e
        
        ds = map (Name "d" Nothing) [1 .. length tva]

        as = map (\(d, i) -> Lang.Id d $ TyConApp lh [TyVar i]) (zip ds tva)
    in
    if not (hasLHTC lh e) then foldr Lam e as else e

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
addToType _ e = error $ "Non Var in addToType"

typeToLHTypeClass :: TypeClasses -> [(Type, Lang.Id)] -> Name -> Type -> Expr
typeToLHTypeClass tc ti lh t =
    case lookupTCDict tc lh t of
        Just lh -> Var lh
        Nothing -> case lookup t ti of
            Just lh -> Var lh
            Nothing -> Var (Lang.Id (Name "BAD" Nothing 0) TyBottom)-- TODO : Can hit this when have TyFun... -- error $ "Typeclass not found in typeToLHTypeClass" ++ show t

type SpecTypeFunc = Name -> Expr -> SpecType -> State -> State

addAssertSpecType :: Expr -> ExprEnv -> TCValues -> SpecTypeFunc
addAssertSpecType conn meenv tcv n e st (s@State { expr_env = eenv
                                        , type_env = tenv
                                        , name_gen = ng
                                        , known_values = kv}) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        st' = convertAssertSpecType conn tcv (s { expr_env = meenv }) st b'
        newE = 
            insertInLams 
                (\is e' -> 
                    Let [(b, e')] $ Lang.Assert (mkApp $ st':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng''}

addAssumeAssertSpecType :: Expr -> ExprEnv -> TCValues -> SpecTypeFunc
addAssumeAssertSpecType conn meenv tcv n e st (s@State { expr_env = eenv
                                                       , type_env = tenv
                                                       , name_gen = ng
                                                       , known_values = kv}) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        assumest' = convertAssumeSpecType (mkAnd meenv) tcv (s { expr_env = meenv }) st
        assertst' = convertAssertSpecType conn tcv (s { expr_env = meenv }) st b'
        newE =
            insertInLams 
                (\is e' -> 
                    Let [(b, e')] $ Lang.Assume (mkApp $ assumest':map Var is)
                                  $ Lang.Assert (mkApp $ assertst':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng''}

-- | convertSpecType
-- We create an Expr from a SpecType in two phases.  First, we create outer
-- lambda expressions, then we create a conjunction of m boolean expressions
-- describing allowed  values of the bound variables
convertAssertSpecType :: Expr -> TCValues -> State -> SpecType -> Lang.Id -> Expr
convertAssertSpecType conn tcv s@(State { known_values = kv
                                        , expr_env = eenv 
                                        , type_env = tenv
                                        , type_classes = tc }) st ret =
    let
        lh = lhTC tcv

        tva = nub . filter isTyVar $ specTypeLamTypes tenv st
        lhtc = map (\t -> TyConApp lh [t]) tva

        dsnames = map (Name "d" Nothing) [0 .. (length tva - 1)]
        nt = (zip dsnames lhtc)

        ds = map (\(n, t) -> Id n t) nt
        dclams = foldr (.) id (map Lam ds) 

        lams = specTypeLams tenv st 
        lams' = dclams . lams . Lam ret
        apps = specTypeApps conn st tcv s (M.fromList nt) ret
    in
    primInject $ lams' apps

convertAssumeSpecType :: Expr -> TCValues -> State -> SpecType -> Expr
convertAssumeSpecType conn tcv s@(State { known_values = kv
                                        , expr_env = eenv 
                                        , type_env = tenv
                                        , type_classes = tc }) st =
    let
        lh = lhTC tcv

        tva = nub . filter isTyVar $ specTypeLamTypes tenv st
        lhtc = map (\t -> TyConApp lh [t]) tva

        dsnames = map (Name "d" Nothing) [0 .. (length tva - 1)]
        nt = (zip dsnames lhtc)

        ds = map (\(n, t) -> Id n t) nt
        dclams = foldr (.) id (map Lam ds) 

        lams = specTypeLams tenv st 
        lams' = dclams . lams
        apps = assumeSpecTypeApps conn st tcv s (M.fromList nt)
    in
    primInject $ lams' apps

specTypeLams :: TypeEnv -> SpecType -> (Expr -> Expr)
specTypeLams tenv (RVar {}) = id
specTypeLams tenv (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType tenv fin
        i = convertSymbolT b t
    in
    Lam i . specTypeLams tenv fout
specTypeLams tenv (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        s = rtvInfoSymbol info

        i = mkId v
    in
    Lam i . specTypeLams tenv rty
specTypeLams tenv r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams tenv r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams tenv rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType tenv c
    in
    id
specTypeLams tenv r = error (show $ PPR.rtypeDoc Full r)

specTypeLamTypes :: TypeEnv -> SpecType -> [Type]
specTypeLamTypes tenv (RVar {}) = []
specTypeLamTypes tenv (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType tenv fin
        i = convertSymbolT b t
    in
    typeOf i:specTypeLamTypes tenv fout
specTypeLamTypes tenv (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        i = mkId v
    in
    (TyVar i):specTypeLamTypes tenv rty
specTypeLamTypes tenv r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes tenv r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes tenv rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType tenv c
    in
    []
specTypeLamTypes tenv r = error (show $ PPR.rtypeDoc Full r)

specTypeApps :: Expr -> SpecType -> TCValues -> State -> M.Map Name Type -> Lang.Id -> Expr
specTypeApps conn st tcv s m b =
    let
        ste = specTypeApps' conn st tcv s m b
    in
    foldl1' (\e -> App (App conn e)) $ ste

assumeSpecTypeApps :: Expr -> SpecType -> TCValues -> State -> M.Map Name Type -> Expr
assumeSpecTypeApps conn st tcv s@(State {type_env = tenv, name_gen = ng, known_values = kv}) m =
    let
        (i, _) = freshId TyBottom ng
    in
    case init $ specTypeApps' conn st tcv s m i of
        xs@(_:_) -> foldl1' (\e -> App (App conn e)) xs
        _ -> mkTrue kv tenv

-- conn specifies hot to connect the different pieces of the spec type together,
-- typically either Implies or And
specTypeApps' :: Expr -> SpecType -> TCValues -> State -> M.Map Name Type -> Lang.Id -> [Expr]
specTypeApps' _ rvar@(RVar {rt_var = (RTV var), rt_reft = r}) tcv s m b =
    let
        symb = reftSymbol $ ur_reft r

        i@(Id _ t) = mkId var

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert (idName symbId) (TyVar i) m 

        re = convertLHExpr (reftExpr $ ur_reft r) tcv s m'
    in
    [App (Lam symbId re) (Var b)]
specTypeApps' conn rfun@(RFun {rt_bind = rb, rt_in = fin, rt_out = fout, rt_reft = r}) tcv s@(State { expr_env = eenv, type_env = tenv }) m b =
    -- TODO : rt_reft
    let
        t = specTypeToType tenv fin
        i = convertSymbolT rb t

        m' = M.insert (idName i) t m
    in
    specTypeApps' conn fin tcv s m' i ++ specTypeApps' conn fout tcv s m' b
specTypeApps' conn rallt@(RAllT {rt_tvbind = RTVar (RTV v) tv, rt_ty = rty}) tcv s m b =
    let
        --sy = rtvInfoSymbol tv

        i = mkId v
    in
    specTypeApps' conn rty tcv s m b
specTypeApps' conn rapp@(RApp {rt_tycon = c, rt_reft = r, rt_args = args}) tcv s@(State {expr_env = eenv, type_env = tenv, type_classes = tc}) m b =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType tenv c args
        i = convertSymbolT symb typ

        argsPred = polyPredFunc args eenv tenv tc typ conn tcv s m b

        m' = M.insert (idName i) typ m

        re = convertLHExpr (reftExpr $ ur_reft r) tcv s m'

        an = mkAnd eenv
    in
    [App (App an (App (Lam i re) (Var b))) argsPred]

polyPredFunc :: [SpecType] -> ExprEnv -> TypeEnv -> TypeClasses -> Type -> Expr -> TCValues -> State -> M.Map Name Type -> Lang.Id -> Expr
polyPredFunc args eenv tenv tc typ conn tcv s m b =
    let
        ts = map (specTypeToType tenv) args
        ts' = map Type ts

        args' = map (\a -> polyPredLam conn a tcv s m b) args

        typE = Type typ
        lhDict = lhTCDict eenv tcv tc typ m

        lhDicts = map (\t' -> lhTCDict eenv tcv tc t' m) ts
    in
    mkApp $ [Var $ Id (lhPP tcv) TyBottom, lhDict, typE] ++ lhDicts ++ ts' ++ args' ++ [Var b]


polyPredLam :: Expr -> SpecType -> TCValues -> State -> M.Map Name Type -> Lang.Id -> Expr
polyPredLam conn rapp tcv s@(State {type_env = tenv, name_gen = ng}) m b =
    let
        t = specTypeToType tenv rapp

        (i, _) = freshId t ng
    in
    convertAssertSpecType conn tcv s rapp i -- m i-- l
polyPredLam _ _ _ _ _ _ = error "Unrecognized SpecType in polyPredLam"

replaceLam :: Lang.Id -> Expr -> Expr -> Expr
replaceLam i true = modify (replaceLam' i true)

replaceLam' :: Lang.Id -> Expr -> Expr -> Expr
replaceLam' i true l@(App (Lam _ _) (Var i')) = if i == i' then true else l
replaceLam' _ _ e = e

specTypeToType :: TypeEnv -> SpecType -> Type
specTypeToType tenv (RVar {rt_var = (RTV var)}) =
    let
        i = mkId var
    in
    TyVar i
specTypeToType tenv (RFun {rt_bind = b, rt_in = fin, rt_out = fout}) =
    let
        t = specTypeToType tenv fin
        t' = specTypeToType tenv fout
    in
    TyFun t t'  
-- specTypeToType (RAllT {rt_ty = rty}) = specTypeToType rty
specTypeToType tenv (RApp {rt_tycon = c, rt_args = args}) =
    let
        t = rTyConType tenv c args
    in
    t

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

rTyConType :: TypeEnv -> RTyCon -> [SpecType]-> Type
rTyConType tenv rtc sts = 
    let
        n = case nameModMatch (mkTyConName . rtc_tc $ rtc) tenv of
            Just n' -> n'
            Nothing -> error "Name not found in rTyConType"
    in
    TyConApp n $ map (specTypeToType tenv) sts

rtvInfoSymbol :: RTVInfo a -> Symbol
rtvInfoSymbol (RTVInfo {rtv_name = s}) = s

convertLHExpr :: Ref.Expr -> TCValues -> State -> M.Map Name Type -> Expr
convertLHExpr (ESym (SL t)) _ _ _ = Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) _ (State {known_values = kv, type_env = tenv}) _ = convertCon kv tenv c
convertLHExpr (EVar s) _ (State { expr_env = eenv }) m = Var $ convertSymbol (symbolName s) eenv m
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
convertLHExpr (ENeg e) tcv s@(State { expr_env = eenv, type_classes = tc, known_values = kv }) m =
    let
        e' = convertLHExpr e tcv s m

        t = typeOf e'
        dict = numTCDict kv tc t

        dict' = case dict of
            Just d -> d
            Nothing ->
                case find (tyVarInTyAppHasName (numTC kv) . snd) (M.toList m) of
                    Just (s, _) -> convertSymbol s eenv m
                    Nothing -> error "No num dictionary for negate in convertLHExpr"

        lhdict = lhTCDict eenv tcv tc t m
    in
    mkApp [ mkPrim Negate eenv
          , lhdict
          , Type t
          , Var dict'
          , e']
convertLHExpr (EBin b e e') tcv s@(State { expr_env = eenv, type_classes = tc, known_values = kv }) m =
    let
        lhe = convertLHExpr e tcv s m
        lhe' = convertLHExpr e' tcv s m

        t = typeOf lhe

        dict = numTCDict kv tc t

        numdict = case dict of
            Just d -> d
            Nothing ->
                case find (tyVarInTyAppHasName (numTC kv) . snd) (M.toList m) of
                    Just (s, _) -> convertSymbol s eenv m
                    Nothing -> error "No num dictionary for negate in convertLHExpr"

        lhdict = lhTCDict eenv tcv tc t m
    in
    mkApp [ convertBop b eenv
          , lhdict
          , Type t
          , Var numdict
          , lhe
          , lhe']
convertLHExpr (PAnd es) tcv s@(State { known_values = kv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e tcv s m) es of
        [] -> mkTrue kv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkAnd eenv) e)) (mkTrue kv tenv) es'
convertLHExpr (POr es) tcv s@(State { known_values = kv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e tcv s m) es of
        [] -> mkFalse kv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkOr eenv) e)) (mkFalse kv tenv) es'
convertLHExpr (PNot e) tcv s@(State {expr_env = eenv }) m =
    App (mkNot eenv) $ convertLHExpr e tcv s m
convertLHExpr (PImp e e') tcv s@(State { expr_env = eenv }) m =
    mkApp [mkImplies eenv, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
convertLHExpr (PIff e e') tcv s@(State { expr_env = eenv }) m =
    mkApp [mkIff eenv, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
convertLHExpr (PAtom brel e e') tcv s@(State {expr_env = eenv, type_classes = tc}) m =
    let
        brel' = convertBrel brel tcv

        ec = convertLHExpr e tcv s m
        ec' = convertLHExpr e' tcv s m

        t = returnType ec

        dict = lhTCDict eenv tcv tc t m
    in
    mkApp [brel', dict, Type t, ec, ec']
convertLHExpr e _ _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

convertSymbol :: Name -> ExprEnv -> M.Map Name Type -> Lang.Id
convertSymbol nm@(Name n md _) eenv m =
    let
        t = maybe TyBottom id $ M.lookup nm m
    in
    case E.lookupNameMod n md eenv of
        Just (n', e) -> Id n' (typeOf e)
        Nothing -> Id nm t

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
        (n', "") -> Name (T.unpack n') Nothing 0
        _ -> Name (T.unpack n) (Just $ T.unpack m') 0

convertCon :: KnownValues -> TypeEnv -> Constant -> Expr
convertCon kv tenv (Ref.I i) = App (mkDCInt kv tenv) (Lit . LitInt $ fromIntegral i)
convertCon kv tenv (Ref.R d) = App (mkDCDouble kv tenv) (Lit . LitDouble $ toRational d)

convertBop :: Bop -> ExprEnv -> Expr
convertBop Ref.Plus = mkPlus
convertBop Ref.Minus = mkMinus
convertBop Ref.Times = mkMult
convertBop Ref.Div = mkDiv
convertBop Ref.Mod = undefined
convertBop Ref.RTimes = mkMult
convertBop Ref.RDiv = mkDiv

lhTCDict :: ExprEnv -> TCValues -> TypeClasses -> Type -> M.Map Name Type -> Expr
lhTCDict eenv tcv tc t m =
    case fmap Var $ lookupTCDict tc (lhTC tcv) t of
        Just d -> d
        Nothing -> 
            case find (tyVarInTyAppHasName (lhTC tcv) . snd) (M.toList m) of
                Just (s, _) -> Var $ convertSymbol s eenv m
                Nothing -> error
                    $ "No dictionary in convertLHExpr v = " ++ show (lhTC tcv)  
                                                            ++ "\nt = " ++ show t
                                                            ++ "\n tc = " ++ show tc


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
tyVarInTyAppHasName n t@(TyConApp n' (TyVar (Id _ _):_)) = n == n'
tyVarInTyAppHasName n t = False

typeIdList :: TCValues -> M.Map Name Type -> [(Type, Lang.Id)]
typeIdList tcv =
    map (\(n, t) -> (head $ tyConAppList t, Id n t)) . M.toList . M.filter (tyVarInTyAppHasName (lhTC tcv))

tyConAppList :: Type -> [Type]
tyConAppList (TyConApp _ ts) = ts
tyConAppList _ = []
