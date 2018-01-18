{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion where

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
mergeLHSpecState xs s@(State {expr_env = eenv, name_gen = ng, type_classes = tc}) tcv =
    let
        (meenv, ng') = doRenames (E.keys eenv) ng eenv
        eenv' = addLHTC eenv tc tcv

        s' = mergeLHSpecState' xs meenv tcv (s {expr_env = eenv', name_gen = ng'})
    in
    s' {expr_env = E.union meenv (expr_env s') }

-- | mergeLHSpecState'
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState' :: [(Var, LocSpecType)] -> ExprEnv -> TCValues -> State -> State
mergeLHSpecState' [] _ _ s = s
mergeLHSpecState' ((v,lst):xs) meenv tcv s =
    let
        (Id (Name n m _) _) = mkId v

        g2N = E.lookupNameMod n m (expr_env s)
    in
    case g2N of
        Just (n', e) ->
            mergeLHSpecState' xs  meenv tcv $ addSpecType n' e (val lst) meenv tcv s
        -- We hit a Nothing for certain functions we consider primitives but which
        -- LH has LT assumptions for. E.g. True, False...
        _ -> mergeLHSpecState' xs meenv tcv s

-- addLHTC
-- We add a LH type class dict for all polymorphic variables in all function
-- definitions.
addLHTC :: ExprEnv -> TypeClasses -> TCValues -> ExprEnv
addLHTC eenv tc tcv = 
    let
        lh = lhTC tcv

        eenv' = modifyContainedASTs (addLHTCLams lh) eenv
        eenv'' = modifyContainedASTs (addLHTCCalls tc lh) eenv'
    in
    eenv''

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

        fc' = map (addTCPasses tc lh_dicts lh) fc
    in
    foldr (uncurry replaceASTs) e fc'

isTYPE :: Type -> Bool
isTYPE TYPE = True
isTYPE (TyConApp (Name "TYPE" _ _) _) = True
isTYPE _ = False

isTyVar :: Type -> Bool
isTyVar (TyVar _) = True
isTyVar _ = False

lhDicts :: Name -> Expr -> [(Type, Lang.Id)]
lhDicts lh (Lam i@(Lang.Id _ (TyConApp n [t])) e) =
    if lh == n then (t, i):lhDicts lh e else lhDicts lh e
lhDicts _ _ = []

addTCPasses :: TypeClasses -> [(Type, Lang.Id)] -> Name -> Expr -> (Expr, Expr)
addTCPasses tc ti lh e =
    let
        tva = nub . mapMaybe typeExprType $ passedArgs e

        lht = map (typeToLHTypeClass tc ti lh) tva

        e' = appCenter e
    in
    (e', insertInApp e' lht)

appCenter :: Expr -> Expr
appCenter (App e _) = appCenter e
appCenter e = e


insertInApp :: Expr -> [Expr] -> Expr
insertInApp (App e e') es = App (insertInApp e es) e'
insertInApp e es = foldl' App e es

typeExprType :: Expr -> Maybe Type
typeExprType (Type t) = Just t
typeExprType _ = Nothing

typeToLHTypeClass :: TypeClasses -> [(Type, Lang.Id)] -> Name -> Type -> Expr
typeToLHTypeClass tc ti lh t =
    case lookupTCDict tc lh t of
        Just lh -> Var lh
        Nothing -> case lookup t ti of
            Just lh -> Var lh
            Nothing -> Var (Lang.Id (Name "BAD" Nothing 0) TyBottom)-- TODO : Can hit this when have TyFun... -- error $ "Typeclass not found in typeToLHTypeClass" ++ show t

addSpecType :: Name -> Expr -> SpecType -> ExprEnv -> TCValues -> State -> State
addSpecType n e st meenv tcv (s@State { expr_env = eenv
                                      , type_env = tenv
                                      , name_gen = ng
                                      , known_values = kv}) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        st' = convertSpecType tcv (s { expr_env = meenv }) st b'
        newE = 
            insertInLams 
                (\is e' -> 
                    Let [(b, e')] $ Lang.Assert (mkApp $ st':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng''}

-- | convertSpecType
-- We create an Expr from a SpecType in two phases.  First, we create outer
-- lambda expressions, then we create a conjunction of m boolean expressions
-- describing allowed  values of the bound variables
convertSpecType :: TCValues -> State -> SpecType -> Lang.Id -> Expr
convertSpecType tcv s@(State { known_values = kv
                             , expr_env = eenv 
                             , type_env = tenv
                             , type_classes = tc }) st ret =
    let
        lh = lhTC tcv

        tva = nub . filter isTyVar $ specTypeLamTypes st
        lhtc = map (\t -> TyConApp lh [t]) tva

        dsnames = map (Name "d" Nothing) [0 .. (length tva - 1)]
        nt = (zip dsnames lhtc)

        ds = map (\(n, t) -> Id n t) nt
        dclams = foldr (.) id (map Lam ds) 

        lams = specTypeLams st 
        lams' = dclams . lams . Lam ret
        apps = specTypeApps st tcv s (M.fromList nt) ret
    in
    primInject $ lams' apps

specTypeLams :: SpecType -> (Expr -> Expr)
specTypeLams (RVar {}) = id
specTypeLams (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType fin
        i = convertSymbolT b t
    in
    Lam i . specTypeLams fout
specTypeLams (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        s = rtvInfoSymbol info

        i = mkId v
    in
    Lam i . specTypeLams rty
specTypeLams r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c
    in
    id
specTypeLams r = error (show $ PPR.rtypeDoc Full r)

specTypeLamTypes :: SpecType -> [Type]
specTypeLamTypes (RVar {}) = []
specTypeLamTypes (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType fin
        i = convertSymbolT b t
    in
    typeOf i:specTypeLamTypes fout
specTypeLamTypes (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        s = rtvInfoSymbol info

        i = mkId v
    in
    typeOf i:specTypeLamTypes rty
specTypeLamTypes r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLamTypes rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c
    in
    []
specTypeLamTypes r = error (show $ PPR.rtypeDoc Full r)


specTypeApps :: SpecType -> TCValues -> State -> M.Map Name Type -> Lang.Id -> Expr
specTypeApps (RVar {rt_var = (RTV var), rt_reft = r}) tcv s m b =
    let
        symb = reftSymbol $ ur_reft r

        i@(Id _ t) = mkId var

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert (idName symbId) (TyVar i) m 

        re = convertLHExpr (reftExpr $ ur_reft r) tcv s m'
    in
    App (Lam symbId re) (Var b)
specTypeApps (RFun {rt_bind = rb, rt_in = fin, rt_out = fout, rt_reft = r}) tcv s@(State { expr_env = eenv }) m b =
    -- TODO : rt_reft
    let
        t = specTypeToType fin
        i = convertSymbolT rb t

        m' = M.insert (idName i) t m
    in
    mkApp [ mkImplies eenv
          , specTypeApps fin tcv s m' i
          , specTypeApps fout tcv s m' b]
specTypeApps (RAllT {rt_tvbind = RTVar (RTV v) tv, rt_ty = rty}) tcv s m b =
    let
        --sy = rtvInfoSymbol tv

        -- i = mkId v
    in
    specTypeApps rty tcv s m b
specTypeApps (RApp {rt_tycon = c, rt_reft = r, rt_args = args}) tcv s m b =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c args
        i = convertSymbolT symb typ

        m' = M.insert (idName i) typ m

        re = convertLHExpr (reftExpr $ ur_reft r) tcv s m'
    in
    App (Lam i re) (Var b)

specTypeToType :: SpecType -> Type
specTypeToType (RVar {rt_var = (RTV var)}) =
    let
        i = mkId var
    in
    TyVar i
specTypeToType (RFun {rt_bind = b, rt_in = fin, rt_out = fout}) =
    let
        t = specTypeToType fin
        t' = specTypeToType fout
    in
    TyFun t t'  
-- specTypeToType (RAllT {rt_ty = rty}) = specTypeToType rty
specTypeToType (RApp {rt_tycon = c, rt_args = args}) =
    let
        t = rTyConType c args
    in
    t

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

rTyConType :: RTyCon -> [SpecType]-> Type
rTyConType rtc sts = TyConApp (mkTyConName . rtc_tc $ rtc) $ map specTypeToType sts

rtvInfoSymbol :: RTVInfo a -> Symbol
rtvInfoSymbol (RTVInfo {rtv_name = s}) = s

convertLHExpr :: Ref.Expr -> TCValues -> State -> M.Map Name Type -> Expr
convertLHExpr (ESym (SL t)) _ _ _ = Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) _ (State {known_values = kv, type_env = tenv}) _ = convertCon kv tenv c
convertLHExpr (EVar s) _ (State { expr_env = eenv }) m = Var $ convertSymbol (symbolName s) eenv m
convertLHExpr (EApp e e') tcv s m =
    case (convertLHExpr e' tcv s m) of
        v@(Var (Id _ (TyConApp _ ts))) -> mkApp $ (convertLHExpr e tcv s m):(map Type ts) ++ [v]
        e'' -> App (convertLHExpr e tcv s m) e''
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

    in
    mkApp [ mkPrim Negate eenv
          , Type t
          , Var dict'
          , e']
convertLHExpr (EBin b e e') tcv s m =
    mkApp [convertBop b, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
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
convertLHExpr (PIff e e') tcv s@(State { expr_env = eenv }) m =
    mkApp [mkIff eenv, convertLHExpr e tcv s m, convertLHExpr e' tcv s m]
convertLHExpr (PAtom brel e e') tcv s@(State {expr_env = eenv, type_classes = tc}) m =
    let
        brel' = convertBrel brel tcv

        ec = convertLHExpr e tcv s m
        ec' = convertLHExpr e' tcv s m

        t = typeOf ec

        dict = 
            case brelTCDict brel tcv tc t of
                Just d -> d
                Nothing -> 
                    case find (tyVarInTyAppHasName (brelTCDictName brel tcv) . snd) (M.toList m) of
                        Just (s, _) -> Var $ convertSymbol s eenv m
                        Nothing -> error
                            $ "No dictionary in convertLHExpr\nm=" ++ (show $ M.toList m) 
                                ++ "\nv = " ++ show (brelTCDictName brel tcv) 
                                -- ++ "\nec = " ++ show ec 
                                ++ "\nt = " ++ show t
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

convertBop :: Bop -> Expr
convertBop _ = undefined

brelTCDictName :: Brel -> TCValues -> Lang.Name
brelTCDictName Ref.Eq tcv = lhTC tcv
brelTCDictName Ref.Ne tcv = lhTC tcv
brelTCDictName Ref.Gt tcv = lhTC tcv
brelTCDictName Ref.Ge tcv = lhTC tcv
brelTCDictName Ref.Lt tcv = lhTC tcv
brelTCDictName Ref.Le tcv = lhTC tcv

brelTCDict :: Brel -> TCValues -> TypeClasses -> Type -> Maybe Expr
brelTCDict Ref.Eq tcv tc = fmap Var . lookupTCDict tc (lhTC tcv) -- eqTCDict kv tc
brelTCDict Ref.Ne tcv tc = fmap Var . lookupTCDict tc (lhTC tcv) -- eqTCDict kv tc d
brelTCDict Ref.Gt tcv tc = fmap Var . lookupTCDict tc (lhTC tcv)
brelTCDict Ref.Ge tcv tc = fmap Var . lookupTCDict tc (lhTC tcv)
brelTCDict Ref.Lt tcv tc = fmap Var . lookupTCDict tc (lhTC tcv)
brelTCDict Ref.Le tcv tc = fmap Var . lookupTCDict tc (lhTC tcv)

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