{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language as Lang
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Execution
import G2.Internals.SMT

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

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> String -> Int -> IO [(State, [Rule], [Expr], Expr)]
findCounterExamples proj primF fp entry steps = do
    ghcInfos <- getGHCInfos [fp]
    let specs = funcSpecs ghcInfos

    (bnds, tycons) <- translationPrimDefs proj fp primF
    let init_state = initState bnds tycons Nothing Nothing Nothing True entry

    let merged_state = mergeLHSpecState specs init_state

    -- putStrLn $ pprExecStateStr merged_state

    hhp <- getZ3ProcessHandles

    run smt2 hhp steps merged_state

getGHCInfos :: [FilePath] -> IO [GhcInfo]
getGHCInfos fp = do
    config <- getOpts []
    return . fst =<< LHI.getGhcInfos Nothing config fp
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkId v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

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
        (meenv, ng') = renameAll eenv ng

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
addSpecType n e st meenv (s@State {expr_env = eenv, name_gen = ng}) =
    let
        (b, ng') = freshId (returnType e) ng

        (b', ng'') = freshId (returnType e) ng'

        st' = convertSpecType meenv st b'
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
convertSpecType :: ExprEnv -> SpecType  -> Lang.Id -> Expr
convertSpecType eenv st ret =
    let
        lams = specTypeLams st . Lam ret
        apps = specTypeApps st eenv M.empty ret
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

specTypeApps :: SpecType -> ExprEnv -> M.Map Symbol Type -> Lang.Id -> Expr
specTypeApps (RVar {rt_var = (RTV var), rt_reft = r}) eenv m b =
    let
        symb = reftSymbol $ ur_reft r

        i@(Id _ t) = mkId var

        symbId = convertSymbolT symb (TyVar i)

        m' = M.insert symb (TyVar i) m 

        re = convertLHExpr (reftExpr $ ur_reft r) eenv m'
    in
    App (Lam symbId re) (Var b)
specTypeApps (RFun {rt_bind = rb, rt_in = fin, rt_out = fout, rt_reft = r}) eenv m b =
    -- TODO : rt_reft
    let
        t = specTypeToType fin
        i = convertSymbolT rb t

        m' = M.insert rb t m
    in
    mkApp [ mkImplies eenv
          , specTypeApps fin eenv m' i
          , specTypeApps fout eenv m' b]
specTypeApps (RAllT {rt_tvbind = RTVar (RTV v) tv, rt_ty = rty}) eenv m b =
    let
        i = mkId v
    in
    specTypeApps rty eenv m b
specTypeApps (RApp {rt_tycon = c, rt_reft = r, rt_args = args}) eenv m b =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c args
        i = convertSymbolT symb typ

        m' = M.insert symb typ m

        re = convertLHExpr (reftExpr $ ur_reft r) eenv m'
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

convertLHExpr :: Ref.Expr -> ExprEnv -> M.Map Symbol Type -> Expr
convertLHExpr (ESym (SL t)) _ _ = Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) _ _ = convertCon c
convertLHExpr (EVar s) _ m = Var $ convertSymbol s m
convertLHExpr (EApp e e') eenv m = App (convertLHExpr e eenv m) (convertLHExpr e' eenv m)
convertLHExpr (ENeg e) eenv m = App (Prim Negate TyBottom) $ convertLHExpr e eenv m
convertLHExpr (EBin b e e') eenv m =
    mkApp [convertBop b, convertLHExpr e eenv m, convertLHExpr e' eenv m]
convertLHExpr (PAnd es) eenv m = 
    case map (\e -> convertLHExpr e eenv m) es of
        [] -> Lit $ LitBool True
        [e] -> e
        es' -> foldr1 (\e -> App (App (mkAnd eenv) e)) es'
convertLHExpr (POr es) eenv m = 
    case map (\e -> convertLHExpr e eenv m) es of
        [] -> Lit $ LitBool False
        [e] -> e
        es' -> foldr1 (\e -> App (App (mkOr eenv) e)) es'
convertLHExpr (PIff e e') eenv m =
    mkApp [mkIff eenv, convertLHExpr e eenv m, convertLHExpr e' eenv m]
convertLHExpr (PAtom brel e e') eenv m =
    mkApp [ mkPrim (convertBrel brel) eenv
          , Var $ Id (Name "TYPE" Nothing 0) TYPE -- TODO: What should this be?
          , Var $ Id (Name "$fordInt" Nothing 0) TyBottom -- TODO: What should this be?
          , convertLHExpr e eenv m
          , convertLHExpr e' eenv m]
convertLHExpr e _ _ = error $ "Unrecognized in convertLHExpr " ++ show e

convertSymbol :: Symbol -> M.Map Symbol Type -> Lang.Id
convertSymbol s m =
    let
        t = M.lookup s m
    in
    convertSymbolT s (maybe TyBottom id t)

convertSymbolT :: Symbol -> Type -> Lang.Id
convertSymbolT s = Id (Name (symbolSafeString s) Nothing 0)

convertCon :: Constant -> Expr
convertCon (Ref.I i) = Lit $ LitInt (fromIntegral i)

convertBop :: Bop -> Expr
convertBop _ = undefined

convertBrel :: Brel -> Primitive
convertBrel Ref.Eq = Lang.Eq
convertBrel Ref.Ne = Lang.Neq
convertBrel Ref.Gt = Lang.Gt
convertBrel Ref.Ge = Lang.Ge
convertBrel Ref.Lt = Lang.Lt
convertBrel Ref.Le = Lang.Le