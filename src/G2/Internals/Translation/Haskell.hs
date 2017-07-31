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

import qualified Data.Maybe as MB

mkIOString :: (Outputable a) => a -> IO String
mkIOString obj = runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    return (showPpr dflags obj)

type CompileClosure = ([(ModSummary, ModGuts)], DynFlags, HscEnv)

hskToG2 :: FilePath -> FilePath -> IO ([G2.Bind], [G2.TyCon])
hskToG2 proj src = do
    (sums_gutss, _, _) <- mkCompileClosure proj src
    let gutss = map snd sums_gutss
    let bnds  = concatMap (map mkBinding . mg_binds) gutss
    let tcs   = concatMap (map mkTyCon . mg_tcs) gutss
    return (bnds, tcs)

mkCompileClosure :: FilePath -> FilePath -> IO CompileClosure
mkCompileClosure proj src = runGhc (Just libdir) $ do
    beta_flags <- getSessionDynFlags
    let dflags = beta_flags { importPaths = [proj] }
    _          <- setSessionDynFlags dflags
    env        <- getSession
    target     <- guessTarget src Nothing
    _          <- setTargets [target]
    _          <- load LoadAllTargets
    -- Now that things are loaded, make the compilation closure.
    mod_graph  <- getModuleGraph
    pmods      <- mapM parseModule mod_graph
    tmods      <- mapM typecheckModule pmods
    dmods      <- mapM desugarModule tmods
    let m_gtss = map coreModule dmods
    let zipd   = (zip mod_graph m_gtss, dflags, env)
    return zipd

mkBinding :: CoreBind -> G2.Bind
mkBinding (NonRec var expr) = G2.Bind G2.NonRec [(mkId var, mkExpr expr)]
mkBinding (Rec ves)         = G2.Bind G2.Rec (map (\(v, e) ->
                                                       (mkId v, mkExpr e)) ves)

mkExpr :: CoreExpr -> G2.Expr
mkExpr (Var var)              = filterPrimOp (mkId var)
mkExpr (Lit lit)              = G2.Lit (mkLit lit)
mkExpr (App fxpr axpr)        = G2.App (mkExpr fxpr) (mkExpr axpr)
mkExpr (Lam var expr)         = G2.Lam (mkId var) (mkExpr expr)
mkExpr (Let bnd expr)         = G2.Let (mkBind bnd) (mkExpr expr)
mkExpr (Case mxpr var _ alts) = G2.Case (mkExpr mxpr) (mkId var) (mkAlts alts)
mkExpr (Cast expr _)          = mkExpr expr
mkExpr (Tick _ expr)          = mkExpr expr
mkExpr (Type ty)              = G2.Type (mkType ty)
mkExpr (Coercion _)           = error "mkExpr: Coercion"

mkId :: Id -> G2.Id
mkId vid = G2.Id ((mkName . V.varName) vid) ((mkType . varType) vid)

filterPrimOp :: G2.Id -> G2.Expr
filterPrimOp (G2.Id name ty) = expr
  where G2.Name occ mb_mdl _ _ = name
        ghc_tys = "GHC.Types"
        expr = case (mb_mdl == Just ghc_tys, occ) of
                    (True, ">=")  -> G2.Prim G2.PGE
                    (True, ">")   -> G2.Prim G2.PGT
                    (True, "==")  -> G2.Prim G2.PEQ
                    (True, "<=")  -> G2.Prim G2.PLE
                    (True, "<")   -> G2.Prim G2.PLT
                    (True, "&&")  -> G2.Prim G2.PAND
                    (True, "||")  -> G2.Prim G2.POR
                    (True, "not") -> G2.Prim G2.PNOT
                    (True, "+")   -> G2.Prim G2.PPlus
                    (True, "-")   -> G2.Prim G2.PMinus
                    (True, "*")   -> G2.Prim G2.PMult
                    (True, "/")   -> G2.Prim G2.PDiv
                    _ -> G2.Var (G2.Id name ty)

mkName :: Name -> G2.Name
mkName name = G2.Name occ mdl ns unq
  where occ = (occNameString . nameOccName) name
        ns  = (mkNameSpace . occNameSpace . nameOccName) name
        unq = (getKey . nameUnique) name
        mdl = case nameModule_maybe name of
                  Nothing -> Nothing
                  Just md -> Just ((moduleNameString . moduleName) md)

mkNameSpace :: NameSpace -> G2.NameSpace
mkNameSpace ns | isVarNameSpace ns     = G2.VarNSpace
               | isTvNameSpace  ns     = G2.TvNSpace
               | isDataConNameSpace ns = G2.DataNSpace
               | isTcClsNameSpace ns   = G2.TcClsNSpace
               | otherwise             = error "mkNameSpace: unrecognized"

mkLit :: Literal -> G2.Lit
mkLit (MachChar chr)     = G2.LitChar chr
mkLit (MachStr bstr)     = G2.LitString (show bstr)
mkLit (MachInt i)        = G2.LitInt (fromInteger i)
mkLit (MachInt64 i)      = G2.LitInt (fromInteger i)
mkLit (MachWord i)       = G2.LitInt (fromInteger i)
mkLit (MachWord64 i)     = G2.LitInt (fromInteger i)
mkLit (MachFloat rat)    = G2.LitFloat rat
mkLit (MachDouble rat)   = G2.LitDouble rat
mkLit (LitInteger i _)   = G2.LitInt (fromInteger i)
mkLit (MachNullAddr)     = error "mkLit: MachNullAddr"
mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: CoreBind -> G2.Bind
mkBind (NonRec var expr) = G2.Bind (G2.NonRec) [(mkId var, mkExpr expr)]
mkBind (Rec ves)         = G2.Bind (G2.Rec) (map (\(v, e) ->
                                                   (mkId v, mkExpr e)) ves)

mkAlts :: [CoreAlt] -> [G2.Alt]
mkAlts alts = map mkAlt alts

mkAlt :: CoreAlt -> G2.Alt
mkAlt (acon, prms, expr) = G2.Alt (mkAltCon acon) (map mkId prms) (mkExpr expr)

mkAltCon :: AltCon -> G2.AltCon
mkAltCon (DataAlt dcon) = G2.DataAlt (mkData dcon)
mkAltCon (LitAlt lit)   = G2.DataAlt (G2.PrimCon (mkLitCon lit))
mkAltCon (DEFAULT)      = G2.Default

mkLitCon :: Literal -> G2.LitCon
mkLitCon (MachChar _)       = G2.C
mkLitCon (MachInt _)        = G2.I
mkLitCon (MachInt64 _)      = G2.I
mkLitCon (MachWord _)       = G2.I
mkLitCon (MachWord64 _)     = G2.I
mkLitCon (MachFloat _)      = G2.F
mkLitCon (MachDouble _)     = G2.D
mkLitCon (LitInteger _ _)   = G2.I
mkLitCon (MachStr _)        = error "mkLitCon: MachStr"
mkLitCon (MachNullAddr)     = error "mkLitCon: MachNullAddr"
mkLitCon (MachLabel _ _ _ ) = error "mkLitCon: MachLabel"

mkType :: Type -> G2.Type
mkType (TyVarTy v)      = G2.TyVarTy (mkName (V.varName v))
mkType (AppTy t1 t2)    = G2.TyApp (mkType t1) (mkType t2)
mkType (TyConApp tc ts) = G2.TyConApp (mkTyCon tc) (map mkType ts)
mkType (ForAllTy b ty)  = G2.TyForAll (mkTyBinder b) (mkType ty)
mkType (LitTy _)        = error "mkType: LitTy"
mkType (CastTy _ _)     = error "mkType: CastTy"
mkType (CoercionTy _)   = error "mkType: Coercion"

mkTyCon :: TyCon -> G2.TyCon
mkTyCon tc | isFunTyCon         tc = G2.FunTyCon     name tcbndrs
           | isAlgTyCon         tc = G2.AlgTyCon     name tvnames algrhs
           | isFamilyTyCon      tc = G2.FamilyTyCon  name tvnames
           | isPrimTyCon        tc = G2.PrimTyCon    name tcbndrs
           | isTypeSynonymTyCon tc = G2.SynonymTyCon name tvnames
           | isPromotedDataCon  tc = G2.Promoted     name tcbndrs dcon
           | otherwise             = error "mkTyCon: unrecognized TyCon"
  where name    = (mkName . tyConName) tc
        algrhs  = (mkAlgTyConRhs . algTyConRhs) tc
        tcbndrs = map mkTyBinder (tyConBinders tc)
        tvnames = map (mkName. V.varName) (tyConTyVars tc)
        dcon    = (mkData . MB.fromJust . isPromotedDataCon_maybe) tc

mkData :: DataCon -> G2.DataCon
mkData datacon = filterPrimCon (G2.DataCon name ty tys)
  where name = mkDataName datacon
        ty   = (mkType . dataConRepType) datacon
        tys  = map mkType (dataConOrigArgTys datacon)

filterPrimCon :: G2.DataCon -> G2.DataCon
filterPrimCon (G2.PrimCon lcon)        = G2.PrimCon lcon
filterPrimCon (G2.DataCon name ty tys) = dcon
  where G2.Name occ mb_mdl _ _ = name
        ghc_tys = "GHC.Types"
        dcon    = case (mb_mdl == Just ghc_tys, occ) of
                      (True, "I#") -> G2.PrimCon G2.I
                      (True, "D#") -> G2.PrimCon G2.D
                      (True, "F#") -> G2.PrimCon G2.F
                      (True, "C#") -> G2.PrimCon G2.C
                      (True, "True") -> G2.PrimCon G2.PTrue
                      (True, "False") -> G2.PrimCon G2.PFalse
                      _  -> G2.DataCon name ty tys

mkDataName :: DataCon -> G2.Name
mkDataName datacon = (mkName . dataConName) datacon

mkTyBinder :: TyBinder -> G2.TyBinder
mkTyBinder (Anon _)    = G2.AnonTyBndr
mkTyBinder (Named v _) = G2.NamedTyBndr (mkName (V.varName v))

mkAlgTyConRhs :: AlgTyConRhs -> G2.AlgTyRhs
mkAlgTyConRhs (AbstractTyCon b)            = G2.AbstractTyCon b
mkAlgTyConRhs (DataTyCon {data_cons = ds}) = G2.DataTyCon  (map mkDataName ds)
mkAlgTyConRhs (TupleTyCon {data_con = d})  = G2.TupleTyCon (mkDataName d)
mkAlgTyConRhs (NewTyCon {data_con = d})    = G2.NewTyCon   (mkDataName d)

