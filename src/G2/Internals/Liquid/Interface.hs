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
import Data.Foldable
import qualified Data.Map as M
import qualified Data.Text as T

import Debug.Trace

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: FilePath -> FilePath -> FilePath -> String -> IO [(State, [Rule], [Expr], Expr)]
findCounterExamples proj prims fp entry = do
    ghcInfos <- getGHCInfos [fp]
    let specs = funcSpecs ghcInfos

    (binds, tycons) <- translationPrimDefs proj fp prims
    let init_state = initState binds tycons Nothing Nothing Nothing True entry

    let merged_state = mergeLHSpecState specs init_state

    putStrLn $ pprExecStateStr merged_state

    hhp <- getZ3ProcessHandles

    run smt2 hhp 200 merged_state

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
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState :: [(Var, LocSpecType)] -> State -> State
mergeLHSpecState [] s = s
mergeLHSpecState ((v,lst):xs) s =
    let
        (Id (Name n m _) _) = mkId v

        g2N = E.lookupNameMod n m (expr_env s)
    in
    case g2N of
        Just (n', e) -> mergeLHSpecState xs $ addSpecType n' e (val lst) s
        -- We hit a Nothing for certain functions we consider primitives but which
        -- LH has LT assumptions for. E.g. True, False...
        Nothing -> mergeLHSpecState xs s

addSpecType :: Name -> Expr -> SpecType -> State -> State
addSpecType n e st (s@State {expr_env = eenv, name_gen = ng}) =
    let
        (b, ng') = freshId (returnType e) ng

        st' = convertSpecType eenv st
        newE = 
            insertInLams 
                (\is e' -> Let [(b, e')] $ Lang.Assert (mkApp $ st':map Var is ++ [Var b]) (Var b))
                e
    in
    s { expr_env = E.insert n newE eenv
      , name_gen = ng'}

-- | convertSpecType
-- We create an Expr from a SpecType in two phases.  First, we create outer
-- lambda expressions, then we create a conjunction of boolean expressions
-- describing allowed  values of the bound variables
convertSpecType :: ExprEnv -> SpecType -> Expr
convertSpecType eenv st =
    let
        lams = specTypeLams st
        apps = specTypeApps st eenv M.empty
    in
    primInject $ lams apps

specTypeLams :: SpecType -> (Expr -> Expr)
specTypeLams (RVar {rt_var = (RTV var)}) = Lam $ mkId var
specTypeLams (RFun {rt_in = fin, rt_out = fout}) = specTypeLams fin . specTypeLams fout
specTypeLams (RAllT {rt_ty = rty}) = specTypeLams rty
specTypeLams r@(RAllP {rt_ty = rty}) = error $ "RAllP " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams r@(RAllS {rt_ty = rty}) = error $ "RAllS " ++ (show $ PPR.rtypeDoc Full r)
specTypeLams rapp@(RApp {rt_tycon = c, rt_args = args, rt_reft = r}) =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c
    in
    Lam (convertSymbolT symb typ)
specTypeLams r = error (show $ PPR.rtypeDoc Full r)

-- We use the Map to gather up types for each Var we encounter- we need these
-- to work with the symbols in the Ref.Expr.
specTypeApps :: SpecType -> ExprEnv -> M.Map Symbol Type -> Expr
specTypeApps (RVar {rt_reft = r}) eenv m = convertLHExpr (reftExpr $ ur_reft r) eenv  m
specTypeApps (RFun {rt_in = fin, rt_out = fout}) eenv m =
    App (App (mkAnd eenv) (specTypeApps fin eenv m)) (specTypeApps fout eenv m)
specTypeApps (RAllT {rt_ty = rty}) eenv m = specTypeApps rty eenv m
specTypeApps (RApp {rt_tycon = c, rt_reft = r}) eenv m =
    let
        symb = reftSymbol $ ur_reft r
        typ = rTyConType c

        m' = M.insert symb typ m
    in
    convertLHExpr (reftExpr $ ur_reft r) eenv  m'
specTypeApps r _ _ = error (show $ PPR.rtypeDoc Full r)

reftSymbol :: Reft -> Symbol
reftSymbol = fst . unpackReft

reftExpr :: Reft -> Ref.Expr
reftExpr = snd . unpackReft

unpackReft :: Reft -> (Symbol, Ref.Expr) 
unpackReft = coerce

rTyConType :: RTyCon -> Type
rTyConType rtc = TyConApp (mkTyConName . rtc_tc $ rtc) []

convertLHExpr :: Ref.Expr -> ExprEnv -> M.Map Symbol Type -> Expr
convertLHExpr (ESym (SL t)) _ _ = Var $ Id (Name (T.unpack t) Nothing 0) TyBottom
convertLHExpr (ECon c) _ _ = convertCon c
convertLHExpr (EVar s) _ m = Var $ convertSymbol s m
convertLHExpr (ENeg e) eenv m = App (Prim Negate TyBottom) $ convertLHExpr e eenv m
convertLHExpr (EBin b e e') eenv m =
    mkApp [convertBop b, convertLHExpr e eenv m, convertLHExpr e' eenv m]
convertLHExpr (PAnd es) eenv m = 
    case map (\e -> convertLHExpr e eenv m) es of
        [] -> Lit $ LitBool True
        [e] -> e
        es' -> foldr1 (\e -> App (App (mkAnd eenv) e)) es'
convertLHExpr (PIff e e') eenv m = mkApp [Prim Implies TyBottom, convertLHExpr e eenv m, convertLHExpr e' eenv m]
convertLHExpr (PAtom brel e e') eenv m =
    mkApp [ mkPrim (convertBrel brel) eenv
          , Var $ Id (Name "TYPE" Nothing 0) TyBottom -- TODO: What should this be?
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
convertSymbolT s = Id (Name (symbolString s) Nothing 0)

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