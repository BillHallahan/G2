-- | Haskell Translation
module G2.Internals.Translation.Haskell
    ( CompileClosure
    , mkCompileClosure
    , hskToG2
    , mkIOString
    ) where

import qualified G2.Internals.Language as G2

import CoreSyn
import DataCon
import GHC
import GHC.Paths
import HscTypes
import Literal
import Name
import Outputable
import TyCon
import TyCoRep
import Unique
import Var as V

mkIOString :: (Outputable a) => a -> IO String
mkIOString obj = runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    return (showPpr dflags obj)

type CompileClosure = ([(ModSummary, ModGuts)], DynFlags, HscEnv)

hskToG2 :: FilePath -> FilePath -> IO ([[(G2.Id, G2.Expr)]], [G2.TyCon])
hskToG2 proj src = do
    (sums_gutss, _, _) <- mkCompileClosure proj src
    let gutss = map snd sums_gutss
    let binds = concatMap (map mkBinds . mg_binds) gutss
    let tycons = concatMap (map mkTyCon . mg_tcs) gutss
    return (binds, tycons)

mkCompileClosure :: FilePath -> FilePath -> IO CompileClosure
mkCompileClosure proj src = runGhc (Just libdir) $ do
    beta_flags <- getSessionDynFlags
    let dflags = beta_flags { importPaths = [proj] }
    _ <- setSessionDynFlags dflags
    env <- getSession
    target <- guessTarget src Nothing
    _ <- setTargets [target]
    _ <- load LoadAllTargets
    -- Now that things are loaded, make the compilation closure.
    mod_graph <- getModuleGraph
    pmods <- mapM parseModule mod_graph
    tmods <- mapM typecheckModule pmods
    dmods <- mapM desugarModule tmods
    let mod_gutss = map coreModule dmods
    return (zip mod_graph mod_gutss, dflags, env)

mkBinds :: CoreBind -> [(G2.Id, G2.Expr)]
mkBinds (NonRec var expr) = [(mkId var, mkExpr expr)]
mkBinds (Rec ves) = map (\(v, e) -> (mkId v, mkExpr e)) ves

mkExpr :: CoreExpr -> G2.Expr
mkExpr (Var var) = filterPrimOp (mkId var)
mkExpr (Lit lit) = G2.Lit (mkLit lit)
mkExpr (App fxpr axpr) = G2.App (mkExpr fxpr) (mkExpr axpr)
mkExpr (Lam var expr) = G2.Lam (mkId var) (mkExpr expr)
mkExpr (Let bnd expr) = G2.Let (mkBind bnd) (mkExpr expr)
mkExpr (Case mxpr var _ alts) = G2.Case (mkExpr mxpr) (mkId var) (mkAlts alts)
mkExpr (Cast expr _) = mkExpr expr
mkExpr (Tick _ expr) = mkExpr expr
mkExpr (Type ty) = G2.Type (mkType ty)
mkExpr (Coercion _) = error "mkExpr: Coercion"

mkId :: Id -> G2.Id
mkId vid = G2.Id ((mkName . V.varName) vid) ((mkType . varType) vid)

filterPrimOp :: G2.Id -> G2.Expr
filterPrimOp (G2.Id name ty) = expr
  where
    G2.Name occ mb_mdl _ = name
    ghc_tys = "GHC.Types"
    expr = case (mb_mdl == Just ghc_tys, occ) of
                (True, ">=") -> G2.Prim G2.Ge
                (True, ">") -> G2.Prim G2.Gt
                (True, "==") -> G2.Prim G2.Eq
                (True, "<=") -> G2.Prim G2.Le
                (True, "<") -> G2.Prim G2.Lt
                (True, "&&") -> G2.Prim G2.And
                (True, "||") -> G2.Prim G2.Or
                (True, "not") -> G2.Prim G2.Not
                (True, "+") -> G2.Prim G2.Plus
                (True, "-") -> G2.Prim G2.Minus
                (True, "*") -> G2.Prim G2.Mult
                (True, "/") -> G2.Prim G2.Div
                _ -> G2.Var (G2.Id name ty)

mkName :: Name -> G2.Name
mkName name = G2.Name occ mdl unq
  where
    occ = (occNameString . nameOccName) name
    unq = (getKey . nameUnique) name
    mdl = case nameModule_maybe name of
              Nothing -> Nothing
              Just md -> Just ((moduleNameString . moduleName) md)

mkLit :: Literal -> G2.Lit
mkLit (MachChar chr) = G2.LitChar chr
mkLit (MachStr bstr) = G2.LitString (show bstr)
mkLit (MachInt i) = G2.LitInt (fromInteger i)
mkLit (MachInt64 i) = G2.LitInt (fromInteger i)
mkLit (MachWord i) = G2.LitInt (fromInteger i)
mkLit (MachWord64 i) = G2.LitInt (fromInteger i)
mkLit (MachFloat rat) = G2.LitFloat rat
mkLit (MachDouble rat) = G2.LitDouble rat
mkLit (LitInteger i _) = G2.LitInt (fromInteger i)
mkLit (MachNullAddr) = error "mkLit: MachNullAddr"
mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: CoreBind -> [(G2.Id, G2.Expr)]
mkBind (NonRec var expr) = [(mkId var, mkExpr expr)]
mkBind (Rec ves) = map (\(v, e) -> (mkId v, mkExpr e)) ves

mkAlts :: [CoreAlt] -> [G2.Alt]
mkAlts alts = map mkAlt alts

mkAlt :: CoreAlt -> G2.Alt
mkAlt (acon, prms, expr) = G2.Alt (mkAltCon acon) (map mkId prms) (mkExpr expr)

mkAltCon :: AltCon -> G2.AltCon
mkAltCon (DataAlt dcon) = G2.DataAlt (mkData dcon)
mkAltCon (LitAlt lit) = G2.DataAlt (G2.PrimCon (mkLitCon lit))
mkAltCon (DEFAULT) = G2.Default

mkLitCon :: Literal -> G2.LitCon
mkLitCon (MachChar _) = G2.C
mkLitCon (MachInt _) = G2.I
mkLitCon (MachInt64 _) = G2.I
mkLitCon (MachWord _) = G2.I
mkLitCon (MachWord64 _) = G2.I
mkLitCon (MachFloat _) = G2.F
mkLitCon (MachDouble _) = G2.D
mkLitCon (LitInteger _ _) = G2.I
mkLitCon (MachStr _) = error "mkLitCon: MachStr"
mkLitCon (MachNullAddr) = error "mkLitCon: MachNullAddr"
mkLitCon (MachLabel _ _ _ ) = error "mkLitCon: MachLabel"

mkType :: Type -> G2.Type
mkType (TyVarTy v) = G2.TyVar (mkName (V.varName v))
mkType (AppTy t1 t2) = G2.TyApp (mkType t1) (mkType t2)
mkType (TyConApp tc ts) = G2.TyConApp (mkTyCon tc) (map mkType ts)
mkType (ForAllTy b ty) = G2.TyForAll (mkTyBinder b) (mkType ty)
mkType (LitTy _) = error "mkType: LitTy"
mkType (CastTy _ _) = error "mkType: CastTy"
mkType (CoercionTy _) = error "mkType: Coercion"

mkTyCon :: TyCon -> G2.TyCon
mkTyCon tycon = G2.TyCon ((mkName. tyConName) tycon)

mkData :: DataCon -> G2.DataCon
mkData datacon = filterPrimCon (G2.DataCon name ty tys)
  where
    name = mkDataName datacon
    ty   = (mkType . dataConRepType) datacon
    tys  = map mkType (dataConOrigArgTys datacon)

filterPrimCon :: G2.DataCon -> G2.DataCon
filterPrimCon (G2.PrimCon lcon) = G2.PrimCon lcon
filterPrimCon (G2.DataCon name ty tys) = dcon
  where
    G2.Name occ mb_mdl _ = name
    ghc_tys = "GHC.Types"
    dcon = case (mb_mdl == Just ghc_tys, occ) of
               (True, "I#") -> G2.PrimCon G2.I
               (True, "D#") -> G2.PrimCon G2.D
               (True, "F#") -> G2.PrimCon G2.F
               (True, "C#") -> G2.PrimCon G2.C
               (True, "True") -> G2.PrimCon G2.CTrue
               (True, "False") -> G2.PrimCon G2.CFalse
               _ -> G2.DataCon name ty tys

mkDataName :: DataCon -> G2.Name
mkDataName datacon = (mkName . dataConName) datacon

mkTyBinder :: TyBinder -> G2.TyBinder
mkTyBinder (Anon _) = G2.AnonTyBndr
mkTyBinder (Named v _) = G2.NamedTyBndr (mkName (V.varName v))

