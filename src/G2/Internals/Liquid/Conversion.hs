{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Liquid.Conversion where

import G2.Internals.Translation
import G2.Internals.Language as Lang
import G2.Internals.Language.KnownValues
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.Primitives

import G2.Lib.Printers

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import Language.Fixpoint.Types.PrettyPrint
import Language.Fixpoint.Types.Refinements hiding (Expr, I)
import  Language.Fixpoint.Types.Names
import qualified Language.Fixpoint.Types.Refinements as Ref

import TyCon
import Var

import Data.Coerce
import qualified Data.Map as M
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

        st' = convertSpecType kv meenv tenv st b'
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
-- lambda expressions, then we create a conjunction of boolean expressions
-- describing allowed  values of the bound variables
convertSpecType :: KnownValues -> ExprEnv -> TypeEnv -> SpecType -> Lang.Id -> Expr
convertSpecType kv eenv tenv st ret =
    let
        lams = specTypeLams st . Lam ret
        apps = specTypeApps st kv eenv tenv M.empty ret
    in
    primInject $ lams apps

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

specTypeApps :: SpecType -> KnownValues -> ExprEnv -> TypeEnv -> M.Map Symbol Type -> Lang.Id -> Expr
specTypeApps (RVar {rt_var = (RTV var), rt_reft = r}) kv eenv tenv m b =
    let
        symb = reftSymbol $ ur_reft r

        i@(Id _ t) = mkId var

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert symb (TyVar i) m 

        re = convertLHExpr (reftExpr $ ur_reft r) kv eenv tenv m'
    in
    App (Lam symbId re) (Var b)
specTypeApps (RFun {rt_bind = rb, rt_in = fin, rt_out = fout, rt_reft = r}) kv eenv tenv m b =
    -- TODO : rt_reft
    let
        t = specTypeToType fin
        i = convertSymbolT rb t

        m' = M.insert rb t m
    in
    mkApp [ mkImplies eenv
          , specTypeApps fin kv eenv tenv m' i
          , specTypeApps fout kv eenv tenv m' b]
specTypeApps (RAllT {rt_tvbind = RTVar (RTV v) tv, rt_ty = rty}) kv eenv tenv m b =
    let
    	s = rtvInfoSymbol tv

        i = mkId v
    in
    specTypeApps rty kv eenv tenv m b
specTypeApps (RApp {rt_tycon = c, rt_reft = r, rt_args = args}) kv eenv tenv m b =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c args
        i = convertSymbolT symb typ

        m' = M.insert symb typ m

        re = convertLHExpr (reftExpr $ ur_reft r) kv eenv tenv m'
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

convertLHExpr :: Ref.Expr -> KnownValues -> ExprEnv -> TypeEnv -> M.Map Symbol Type -> Expr
convertLHExpr (ESym (SL t)) _ _ _ _ = Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) _ _ _ _ = convertCon c
convertLHExpr (EVar s) _ eenv _ m = Var $ convertSymbol s eenv m
convertLHExpr (EApp e e') kv eenv tenv m =
	case (convertLHExpr e' kv eenv tenv m) of
		v@(Var (Id _ (TyConApp _ ts))) -> mkApp $ (convertLHExpr e kv eenv tenv m):(map Type ts) ++ [v]
		e'' -> App (convertLHExpr e kv eenv tenv m) e''
convertLHExpr (ENeg e) kv eenv tenv m =
    mkApp $ mkPrim Negate eenv
          : Var (Id (Name "TYPE" Nothing 0) TYPE)
          : Var (Id (Name "$fordInt" Nothing 0) TyBottom)
          : [convertLHExpr e kv eenv tenv m]
convertLHExpr (EBin b e e') kv eenv tenv m =
    mkApp [convertBop b, convertLHExpr e kv eenv tenv m, convertLHExpr e' kv eenv tenv m]
convertLHExpr (PAnd es) kv eenv tenv m = 
    case map (\e -> convertLHExpr e kv eenv tenv m) es of
        [] -> mkTrue kv tenv
        [e] -> e
        es' -> foldr1 (\e -> App (App (mkAnd eenv) e)) es'
convertLHExpr (POr es) kv eenv tenv m = 
    case map (\e -> convertLHExpr e kv eenv tenv m) es of
        [] -> mkFalse kv tenv
        [e] -> e
        es' -> foldr1 (\e -> App (App (mkOr eenv) e)) es'
convertLHExpr (PIff e e') kv eenv tenv m =
    mkApp [mkIff eenv, convertLHExpr e kv eenv tenv m, convertLHExpr e' kv eenv tenv m]
convertLHExpr (PAtom brel e e') kv eenv tenv m =
	convertBrel brel (convertLHExpr e kv eenv tenv m) (convertLHExpr e' kv eenv tenv m)
convertLHExpr e _ _ _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

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


convertCon :: Constant -> Expr
convertCon (Ref.I i) = Lit $ LitInt (fromIntegral i)
convertCon (Ref.R d) = Lit $ LitDouble (toRational d)

convertBop :: Bop -> Expr
convertBop _ = undefined

convertBrel :: Brel -> Expr -> Expr -> Expr
convertBrel Ref.Eq = mkLHEq
convertBrel Ref.Ne = mkLHNeq
convertBrel Ref.Gt = mkLHGt
convertBrel Ref.Ge = mkLHGe
convertBrel Ref.Lt = mkLHLt
convertBrel Ref.Le = mkLHLe