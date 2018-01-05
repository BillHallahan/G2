{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion where

import G2.Internals.Translation
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.KnownValues
import G2.Internals.Liquid.Primitives

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import  Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref

import TyCon
import Var hiding (tyVarName)

import Data.Coerce
import Data.List
import qualified Data.Map as M
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
mergeLHSpecState :: [(Var, LocSpecType)] -> State -> State
mergeLHSpecState xs s@(State {expr_env = eenv, name_gen = ng}) =
    let
        (meenv, ng') = doRenames (E.keys eenv) ng eenv

        s' = mergeLHSpecState' xs meenv (s {name_gen = ng'})
    in
    s' {expr_env = E.union (expr_env s') meenv}

-- | mergeLHSpecState'
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState' :: [(Var, LocSpecType)] -> ExprEnv -> State -> State
mergeLHSpecState' [] _ s = s
mergeLHSpecState' ((v,lst):xs) meenv s =
    let
        (Id (Name n m _) _) = mkId v

        g2N = E.lookupNameMod n m (expr_env s)
    in
    trace ("n = " ++ show n ++ "b = " ++ show (noTCDict meenv lst (eqTC $ known_values s) [Ref.Eq, Ref.Ne])) $
    case g2N of
        Just (n', e) ->
            mergeLHSpecState' xs  meenv $ addSpecType n' e (val lst) meenv s
        -- We hit a Nothing for certain functions we consider primitives but which
        -- LH has LT assumptions for. E.g. True, False...
        _ -> mergeLHSpecState' xs meenv s

addSpecType :: Name -> Expr -> SpecType -> ExprEnv -> State -> State
addSpecType n e st meenv (s@State { expr_env = eenv
                                  , type_env = tenv
                                  , name_gen = ng
                                  , known_values = kv}) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        st' = convertSpecType (s { expr_env = meenv }) st b'
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
convertSpecType :: State -> SpecType -> Lang.Id -> Expr
convertSpecType s@(State { known_values = kv
                         , expr_env = eenv 
                         , type_env = tenv }) st ret =
    let
        lams = specTypeLams st . Lam ret
        apps = specTypeApps st s M.empty ret
    in
    primInject $ lams apps

specTypeLams :: SpecType -> (Expr -> Expr)
specTypeLams (RVar {}) = id
specTypeLams (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType fin
        i = convertSymbolT b t
    in
    trace ("i = " ++ show i) Lam i . specTypeLams fout
specTypeLams (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        s = rtvInfoSymbol info

        i = mkId v
    in
    trace ("i2 = " ++ show i) Lam i . specTypeLams rty
specTypeLams r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c
    in
    id
specTypeLams r = error (show $ PPR.rtypeDoc Full r)

specTypeApps :: SpecType -> State -> M.Map Symbol Type -> Lang.Id -> Expr
specTypeApps (RVar {rt_var = (RTV var), rt_reft = r}) s m b =
    let
        symb = reftSymbol $ ur_reft r

        i@(Id _ t) = mkId var

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert symb (TyVar i) m 

        re = convertLHExpr (reftExpr $ ur_reft r) s m'
    in
    App (Lam symbId re) (Var b)
specTypeApps (RFun {rt_bind = rb, rt_in = fin, rt_out = fout, rt_reft = r}) s@(State { expr_env = eenv }) m b =
    -- TODO : rt_reft
    let
        t = specTypeToType fin
        i = convertSymbolT rb t

        m' = M.insert rb t m
    in
    mkApp [ mkImplies eenv
          , specTypeApps fin s m' i
          , specTypeApps fout s m' b]
specTypeApps (RAllT {rt_tvbind = RTVar (RTV v) tv, rt_ty = rty}) s m b =
    let
        --sy = rtvInfoSymbol tv

        -- i = mkId v
    in
    specTypeApps rty s m b
specTypeApps (RApp {rt_tycon = c, rt_reft = r, rt_args = args}) s m b =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c args
        i = convertSymbolT symb typ

        m' = M.insert symb typ m

        re = convertLHExpr (reftExpr $ ur_reft r) s m'
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

convertLHExpr :: Ref.Expr -> State -> M.Map Symbol Type -> Expr
convertLHExpr (ESym (SL t)) _ _ = trace ("v1 = " ++ show (Name (T.unpack t) Nothing 0)) Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) (State {known_values = kv, type_env = tenv}) _ = convertCon kv tenv c
convertLHExpr (EVar s) (State { expr_env = eenv }) m = trace ("v2 = " ++ show (convertSymbol s eenv m)) Var $ convertSymbol s eenv m
convertLHExpr (EApp e e') s m =
    case (convertLHExpr e' s m) of
        v@(Var (Id _ (TyConApp _ ts))) -> mkApp $ (convertLHExpr e s m):(map Type ts) ++ [v]
        e'' -> App (convertLHExpr e s m) e''
convertLHExpr (ENeg e) s@(State { expr_env = eenv }) m =
    mkApp $ mkPrim Negate eenv
          : Var (Id (Name "TYPE" Nothing 0) TYPE)
          : Var (Id (Name "$fordInt" Nothing 0) TyBottom)
          : [convertLHExpr e s m]
convertLHExpr (EBin b e e') s m =
    mkApp [convertBop b, convertLHExpr e s m, convertLHExpr e' s m]
convertLHExpr (PAnd es) s@(State { known_values = kv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e s m) es of
        [] -> mkTrue kv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkAnd eenv) e)) (mkTrue kv tenv) es'
convertLHExpr (POr es) s@(State { known_values = kv, expr_env = eenv, type_env = tenv }) m = 
    case map (\e -> convertLHExpr e s m) es of
        [] -> mkFalse kv tenv
        [e] -> e
        es' -> foldr (\e -> App (App (mkOr eenv) e)) (mkFalse kv tenv) es'
convertLHExpr (PIff e e') s@(State { expr_env = eenv }) m =
    mkApp [mkIff eenv, convertLHExpr e s m, convertLHExpr e' s m]
convertLHExpr (PAtom brel e e') s@(State {known_values = kv, expr_env = eenv, type_classes = tc}) m =
    let
        brel' = convertBrel brel kv

        ec = convertLHExpr e s m
        ec' = convertLHExpr e' s m

        t = typeOf ec

        dict = 
            case brelTCDict brel kv tc t of
                Just d -> d
                Nothing -> 
                    case find (tyVarInTyAppHasName (brelTCDictName brel kv) . snd) (M.toList m) of
                        Just (s, _) -> Var $ convertSymbol s eenv m
                        Nothing -> error
                            $ "No dictionary in convertLHExpr\nm=" ++ (show $ map snd $ M.toList m) 
                                ++ "\nv = " ++ show (brelTCDictName brel kv) 
                                -- ++ "\nec = " ++ show ec 
                                ++ "\nt = " ++ show t
    in
    mkApp [brel', dict, Type t, ec, ec']
convertLHExpr e _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

convertSymbol :: Symbol -> ExprEnv -> M.Map Symbol Type -> Lang.Id
convertSymbol s eenv m =
    let
        t = maybe TyBottom id $ M.lookup s m

        nm@(Name n md _) = symbolName s
    in
    case E.lookupNameMod n md eenv of
        Just (n', _) -> Id n' t
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

brelTCDictName :: Brel -> KnownValues -> Lang.Name
brelTCDictName Ref.Eq = eqTC
brelTCDictName Ref.Ne = eqTC
brelTCDictName Ref.Gt = ordTC
brelTCDictName Ref.Ge = ordTC
brelTCDictName Ref.Lt = ordTC
brelTCDictName Ref.Le = ordTC

brelTCDict :: Brel -> KnownValues -> TypeClasses -> Type -> Maybe Expr
brelTCDict Ref.Eq kv tc = fmap Var . eqTCDict kv tc
brelTCDict Ref.Ne kv tc = fmap Var . eqTCDict kv tc
brelTCDict Ref.Gt kv tc = fmap Var . ordTCDict kv tc
brelTCDict Ref.Ge kv tc = fmap Var . ordTCDict kv tc
brelTCDict Ref.Lt kv tc = fmap Var . ordTCDict kv tc
brelTCDict Ref.Le kv tc = fmap Var . ordTCDict kv tc

convertBrel :: Brel -> KnownValues -> Expr
convertBrel Ref.Eq kv = Var $ Id (eqFunc kv) TyBottom
convertBrel Ref.Ne kv = Var $ Id (neqFunc kv) TyBottom
convertBrel Ref.Gt kv = Var $ Id (gtFunc kv) TyBottom
convertBrel Ref.Ge kv = Var $ Id (geFunc kv) TyBottom
convertBrel Ref.Lt kv = Var $ Id (ltFunc kv) TyBottom
convertBrel Ref.Le kv = Var $ Id (leFunc kv) TyBottom


tyVarInTyAppHasName :: Name -> Type -> Bool
tyVarInTyAppHasName n t@(TyConApp n' (TyVar (Id _ _):_)) = n == n'
tyVarInTyAppHasName n t = False

tyConAppName :: Type -> Maybe Name
tyConAppName (TyConApp n _) = Just n
tyConAppName _ = Nothing

-- addTCDict
-- Adds the given dictionary to all functions in the expression environment that
-- need it, but are not currently passed it.
-- A function might need this dictionary, but not be passed it because:
-- (1) It uses a function from the dictionary only in the specification
-- (2) It calls a function that uses it only in the specification
addTCDict :: ExprEnv -> KnownValues -> [(Name, LocSpecType)] -> Name -> [Brel] -> ExprEnv
addTCDict eenv kv nlst dict brel =
    let
        need = needTCDict eenv nlst dict brel
    in
    undefined


-- needTCDict
-- Returns a list of functions that need the dictionary for the given TC, but
-- are not currently passed it.
needTCDict :: ExprEnv -> [(Name, LocSpecType)] -> Name -> [Brel] -> [Name]
needTCDict eenv nlst dict brel =
    let
        noTC = filter (\(_, lst) -> not . null $ noTCDict eenv lst dict brel) nlst
        noTCNames = map fst noTC
    in
    needTCDict' eenv noTCNames

needTCDict' :: ExprEnv -> [Name] -> [Name]
needTCDict' eenv ns =
    let
        ns' = E.keys $ E.filter (callWithNameIn ns) eenv
    in
    if ns == ns' then ns' else needTCDict' eenv ns'

callWithNameIn :: [Name] -> Expr -> Bool
callWithNameIn ns = coerce . evalASTs (callWithNameIn' ns)

callWithNameIn' :: [Name] -> Expr -> Any
callWithNameIn' ns (Var (Id n _)) = Any $ n `elem` ns
callWithNameIn' _ _ = Any False

-- | noTCDict
-- Returns the names of TyVar-typed argument passed to brel's in l in the SpecType
-- without a passed TypeClass dictionary of type d
noTCDict :: ExprEnv -> LocSpecType -> Name -> [Brel] -> [Name]
noTCDict eenv lst d l =
    let
        st = val lst

        brel = concatMap (\b -> usedBrelSpecTypeWithArg (brelTest eenv) M.empty b st) l

        as = lhArgs st
        asty = map typeOf as
    in
    if not (any (tyConHasName d) asty) then brel else []

-- | lhArgs
-- A list of the arguments to the LH assertion
lhArgs :: SpecType -> [Lang.Id]
lhArgs (RFun {rt_bind = b, rt_in = fin, rt_out = fout, rt_reft = r}) =
    let
        t = specTypeToType fin
        i = convertSymbolT b t
    in
    i:lhArgs fout
lhArgs (RAllT {rt_tvbind = RTVar (RTV v) info, rt_ty = rty}) =
    let
        i = mkId v
    in
    i:lhArgs rty
lhArgs _ = []

-- | usedBrelSpecType
-- Given a LH SpecType, get all Brel's used in the SpecType
usedBrelSpecType :: SpecType -> [Brel]
usedBrelSpecType (RVar { rt_reft = r }) = usedBrelReft r
usedBrelSpecType (RFun { rt_in = rti, rt_out = rto, rt_reft = r }) =
    usedBrelReft r ++ usedBrelSpecType rti ++ usedBrelSpecType rto
usedBrelSpecType (RAllT { rt_ty = r }) = usedBrelSpecType r
-- usedBrelSpecType (RAllP { rt_ty = r}) = usedBrelSpecType r
-- usedBrelSpecType (RAllS { rt_ty = r }) = usedBrelSpecType r
usedBrelSpecType (RApp { rt_args = rargs, rt_reft = r}) = usedBrelReft r ++ concatMap usedBrelSpecType rargs
-- usedBrelSpecType (RAllE { rt_allarg = rtall, rt_ty = rty }) = usedBrelSpecType rtall ++ usedBrelSpecType rty
-- usedBrelSpecType (REx { rt_exarg = rta, rt_ty = rty }) = usedBrelSpecType rta ++ usedBrelSpecType rty
-- usedBrelSpecType (RAppTy {rt_arg = rta, rt_res = rtr, rt_reft = r}) =
    -- usedBrelReft r ++ usedBrelSpecType rta ++ usedBrelSpecType rtr
-- usedBrelSpecType (RRTy { rt_env = rte, rt_ref = r, rt_ty = rty}) =
    -- usedBrelReft r ++ concatMap (usedBrelSpecType . snd) rte ++ usedBrelSpecType rty
-- usedBrelSpecType (RHole r) = usedBrelReft r
-- usedBrelSpecType _ = []

usedBrelReft :: UReft Reft -> [Brel]
usedBrelReft = usedBrelExpr . reftExpr . ur_reft

-- | usedBrelExpr
-- Given a LH Expr, get all Brel's used in the Expr
usedBrelExpr :: Ref.Expr -> [Brel]
usedBrelExpr (EApp e e') = usedBrelExpr e ++ usedBrelExpr e'
usedBrelExpr (ENeg e) = usedBrelExpr e
usedBrelExpr (EBin _ e e') = usedBrelExpr e ++ usedBrelExpr e'
usedBrelExpr (EIte e e' e'') = usedBrelExpr e ++ usedBrelExpr e' ++ usedBrelExpr e''
usedBrelExpr (ECst e _) = usedBrelExpr e
usedBrelExpr (ELam _ e) = usedBrelExpr e
usedBrelExpr (ETApp e _) = usedBrelExpr e
usedBrelExpr (ETAbs e _) = usedBrelExpr e
usedBrelExpr (PAnd e) = concatMap usedBrelExpr e
usedBrelExpr (POr e) = concatMap usedBrelExpr e
usedBrelExpr (PNot e) = usedBrelExpr e
usedBrelExpr (PImp e e') = usedBrelExpr e ++ usedBrelExpr e'
usedBrelExpr (PIff e e') = usedBrelExpr e ++ usedBrelExpr e'
usedBrelExpr (PAtom b e e') = b:(usedBrelExpr e ++ usedBrelExpr e')
usedBrelExpr (PAll _ e) = usedBrelExpr e
usedBrelExpr (PExist _ e) = usedBrelExpr e
usedBrelExpr (PGrad _ _ _ e) = usedBrelExpr e
usedBrelExpr _ = []

-- | usedBrelSpecTypeWithArg
-- Given a LH SpecType, returns if the given Brel is used in the SpecType, where the ith argument
-- satisifies the given predicate
usedBrelSpecTypeWithArg :: (M.Map Symbol Type -> Ref.Expr -> Ref.Expr -> [a]) -> M.Map Symbol Type -> Brel -> SpecType -> [a]
usedBrelSpecTypeWithArg f m b (RVar { rt_var = (RTV var), rt_reft = r }) = 
    let
        symb = reftSymbol $ ur_reft r
        i = mkId var

        m' = M.insert symb (TyVar i) m 
    in
    usedBrelReftWithArg f m' b r
usedBrelSpecTypeWithArg f m b (RFun { rt_in = rti, rt_out = rto, rt_reft = r }) =
    usedBrelReftWithArg f m b r ++ usedBrelSpecTypeWithArg f m b rti ++ usedBrelSpecTypeWithArg f m b rto
usedBrelSpecTypeWithArg f m b (RAllT { rt_ty = r }) = usedBrelSpecTypeWithArg f m b r
usedBrelSpecTypeWithArg f m b (RAllP { rt_ty = r}) = usedBrelSpecTypeWithArg f m b r
usedBrelSpecTypeWithArg f m b (RAllS { rt_ty = r }) = usedBrelSpecTypeWithArg f m b r
usedBrelSpecTypeWithArg f m b (RApp { rt_args = rargs, rt_reft = r}) = 
    usedBrelReftWithArg f m b r ++ concatMap (usedBrelSpecTypeWithArg f m b) rargs
usedBrelSpecTypeWithArg f m b (RAllE { rt_allarg = rtall, rt_ty = rty }) = 
    usedBrelSpecTypeWithArg f m b rtall ++ usedBrelSpecTypeWithArg f m b rty
usedBrelSpecTypeWithArg f m b (REx { rt_exarg = rta, rt_ty = rty }) = 
    usedBrelSpecTypeWithArg f m b rta ++ usedBrelSpecTypeWithArg f m b rty
usedBrelSpecTypeWithArg f m b (RAppTy {rt_arg = rta, rt_res = rtr, rt_reft = r}) =
    usedBrelReftWithArg f m b r ++ usedBrelSpecTypeWithArg f m b rta ++ usedBrelSpecTypeWithArg f m b rtr
usedBrelSpecTypeWithArg f m b (RRTy { rt_env = rte, rt_ref = r, rt_ty = rty}) =
    usedBrelReftWithArg f m b r ++ concatMap (usedBrelSpecTypeWithArg f m b . snd) rte ++ usedBrelSpecTypeWithArg f m b rty
usedBrelSpecTypeWithArg f m b (RHole r) = usedBrelReftWithArg f m b r
usedBrelSpecTypeWithArg _ _ _ _ = []

usedBrelReftWithArg :: (M.Map Symbol Type -> Ref.Expr -> Ref.Expr -> [a]) -> M.Map Symbol Type -> Brel -> UReft Reft -> [a]
usedBrelReftWithArg f m b = usedBrelExprWithArg f m b . reftExpr . ur_reft

-- | usedBrelExpr
-- Given a LH Expr, returns if the given Brel is used in the Expr, where the ith argument
-- satisifies the given predicate
usedBrelExprWithArg :: (M.Map Symbol Type -> Ref.Expr -> Ref.Expr -> [a]) -> M.Map Symbol Type -> Brel -> Ref.Expr -> [a]
usedBrelExprWithArg f m b (EApp e e') =
    usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e'
usedBrelExprWithArg f m b (ENeg e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (EBin _ e e') = 
    usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e'
usedBrelExprWithArg f m b (EIte e e' e'') = 
    usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e' ++ usedBrelExprWithArg f m b e''
usedBrelExprWithArg f m b (ECst e _) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (ELam _ e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (ETApp e _) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (ETAbs e _) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (PAnd e) = concatMap (usedBrelExprWithArg f m b) e
usedBrelExprWithArg f m b (POr e) = concatMap (usedBrelExprWithArg f m b) e
usedBrelExprWithArg f m b (PNot e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (PImp e e') = 
    usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e'
usedBrelExprWithArg f m b (PIff e e') = 
    usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e'
usedBrelExprWithArg f m b (PAtom b' e e') =
    (if b == b' then f m e e' else [])
    ++ usedBrelExprWithArg f m b e ++ usedBrelExprWithArg f m b e'
usedBrelExprWithArg f m b (PAll _ e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (PExist _ e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b (PGrad _ _ _ e) = usedBrelExprWithArg f m b e
usedBrelExprWithArg f m b _ = []

brelTest :: ExprEnv -> M.Map Symbol Type -> Ref.Expr -> Ref.Expr -> [Name]
brelTest eenv m (EVar s) _ =
    tyVarName $ typeOf (convertSymbol s eenv m)
brelTest _ _ _ _ = []

tyVarName :: Type -> [Name]
tyVarName (TyVar (Id n _)) = [n]
tyVarName t = []

tyConHasName :: Name -> Type -> Bool
tyConHasName n (TyConApp n' _) = n == n'
tyConHasName _ _ = False