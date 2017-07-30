-- | Haskell Translation
module G2.Internals.Translation.Haskell
    () where

import qualified G2.Internals.Language as G2
-- import qualified G2.Internals.Translation.HaskellPrelude as P
-- import G2.Internals.Translation.TranslToCore
-- import G2.Internals.Translation.PrimReplace

import CoreSyn
import CoreUtils as CU
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
import Var

import qualified Data.Map   as M
import qualified Data.Maybe as B

mkIOString :: (Outputable a) => a -> IO String
mkIOString obj = runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    return (showPpr dflags obj)

{-
-- | Haskell Source to Core2
--   Streamline the process of converting a list of files into Core2.
hskToG2 :: FilePath -> FilePath
    -> IO (G2.TEnv, G2.EEnv, M.Map G2.Name G2.Name, M.Map G2.Name G2.Name)
hskToG2 proj src = do
    (tenv, eenv) <- hskToTL' proj src
    let names = namesMapTEEnv eenv
    let conNames = namesMapCons tenv
    let (tenv', eenv') = transl tenv eenv
    return (tenv', eenv', names, conNames)

-- | Haskell Source to TL Core
--   Streamline the process of converting a list of files into TL Core.
hskToTL :: FilePath -> FilePath -> IO (TL.TTEnv, TL.TEEnv)
hskToTL proj src = do
    ghc_cores <- mkMultiGHCCore proj src
    return (combineTLCores $ mkMultiTLCore ghc_cores)

hskToTL' :: FilePath -> FilePath -> IO (TL.TTEnv, TL.TEEnv)
hskToTL' proj src = do
    (sums_gutss, _, _) <- mkCompileClosure proj src
    let acc_prog = concatMap (mg_binds . snd) sums_gutss
    let acc_tycs = concatMap (mg_tcs . snd) sums_gutss

    let tenv = mkTEnv (mkTypeEnv (map ATyCon acc_tycs))
    let eenv = mkEEnv acc_prog
    
    return (tenv, eenv)

    -- return $ primReplace (tenv, eenv)

-- | Make Raw Core
--   Make a raw GHC Core given a FilePath (String).
--   Alternate the last two lines to let GHC perform optimizations, or not!
mkGHCCore :: FilePath -> IO CoreModule
mkGHCCore filepath = runGhc (Just libdir) $ do
    setSessionDynFlags =<< getSessionDynFlags
    compileToCoreSimplified filepath  -- Optimizations on.
    -- compileToCoreModule filepath  -- No optimizations.

-- | Make Raw Core
--   Make a raw GHC Core give na FilePath (String).
--   Alternate the last two lines to let GHC perform optimizations, or not!
mkGHCCore' :: FilePath -> FilePath -> IO CoreModule
mkGHCCore' proj src = runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        setSessionDynFlags (dflags {importPaths = [proj]})
        compileToCoreSimplified src
        -- compileToCoreModule src

-- | Make Multiple Cores
--   Make multiple GHC Cores based on import stuff.
mkMultiGHCCore :: FilePath -> FilePath -> IO [CoreModule]
mkMultiGHCCore proj src = do
    deps  <- getDependencies proj src
    cores <- sequence $ map (mkGHCCore' proj) deps
    return cores

-- | Get Dependency List
--   Gets the list of dependencies for the module graph given a single module.
getDependencies :: FilePath -> FilePath -> IO [FilePath]
getDependencies proj src = do
    mod_graph <- runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        setSessionDynFlags (dflags {importPaths = [proj]})
        target <- guessTarget src Nothing
        setTargets [target]
        load LoadAllTargets
        getModuleGraph
    return $ map (B.fromMaybe "" . ml_hs_file . ms_location) mod_graph

-- | Make TL Core
--   Given a GHC Core, we convert it into a TL Core.
mkTLCore :: CoreModule -> (TL.TTEnv, TL.TEEnv)
mkTLCore core = (mkTEnv (cm_types core), mkEEnv (cm_binds core))

-- | Make Multiple TL Cores
mkMultiTLCore :: [CoreModule] -> [(TL.TTEnv, TL.TEEnv)]
mkMultiTLCore cores = map mkTLCore cores

-- | Combine TL Cores
combineTLCores :: [(TL.TTEnv, TL.TEEnv)] -> (TL.TTEnv, TL.TEEnv)
combineTLCores cores = foldl pairjoin (M.empty, M.empty) cores
  where pairjoin (acc_t, acc_e) (t, e) = (M.union acc_t t, M.union acc_e e)

-- | Make Compilation Closure
--   Captures a snapshot of the DynFlags and HscEnv in addition to
--   the ModGuts in the ModuleGraph. This allows compilation to be, intheory,
--   more portable across different applications, since ModGuts is a crucial
--   intermediary for compilation in general.
mkCompileClosure :: FilePath -> FilePath ->
                    IO ([(ModSummary, ModGuts)], DynFlags, HscEnv) 
mkCompileClosure proj src = runGhc (Just libdir) $ do
    beta_flags <- getSessionDynFlags
    let dflags = beta_flags { importPaths = [proj] }
    setSessionDynFlags dflags
    env    <- getSession
    target <- guessTarget src Nothing
    setTargets [target]
    load LoadAllTargets

    mod_graph <- getModuleGraph
    pmods <- (sequence . map parseModule) mod_graph
    tmods <- (sequence . map typecheckModule) pmods
    dmods <- (sequence . map desugarModule) tmods
    let mod_gutss = map coreModule dmods

    let zipd = (zip mod_graph mod_gutss, dflags, env)
    return zipd

-- | Outputable to String
--   Basic printing capabilities for converting an Outputable into a String.
outStr :: (Outputable a) => a -> IO String
outStr obj = runGhc (Just libdir) $ do
    flags <- getSessionDynFlags
    return $ showPpr flags obj

-- | Make Name
--   From a GHC Name, make a raw TL.TName.
mkName :: Name -> TL.TName
-- mkName name = occNameString $ nameOccName name
mkName = mkUniquedName
-- mkName = mkQualName

mkUniquedName :: Name -> TL.TName
mkUniquedName name = (occ_str, unq_int)
  where occ_str = occNameString $ nameOccName name
        unq_int = getKey $ nameUnique name

-- | Make Qualified Name
--   From a GHC Name, make a qualified TL.TName.
-- mkQualName :: Name -> TL.TName
-- mkQualName name = case nameModule_maybe name of
--     Nothing -> raw_name
--     Just md -> (moduleNameString $ moduleName md) ++ mod_sep ++ raw_name
--   where raw_name = occNameString $ nameOccName name

--  mkQualName name = case srcSpanFileName_maybe $ nameSrcSpan name of
--     Just fs -> (occNameString $ nameOccName name)  ++ ".__." ++ (unpackFS fs)
--     Nothing -> occNameString $ nameOccName name

-- | Make Type Environment
--   Make the type environment given a GHC Core.
mkTEnv :: TypeEnv -> TL.TTEnv
mkTEnv tenv = M.fromList $ map mkADT tycons
  where tycons = filter isAlgTyCon $ typeEnvTyCons tenv

-- | Make Algebraic Data Type
--   Given a type constructor, make the corresonding TL ADT instance. Returned
--   as a pair in order to make binding into the type environment easier.
mkADT :: TyCon -> (TL.TName, TL.TType)
mkADT algtc = (gname, TL.TyAlg gname gdcs)
  where name  = tyConName algtc
        dcs   = tyConDataCons algtc
        gname = mkName name
        gdcs  = map mkData dcs

-- | Make Data Constructor
--   Make a TL data constructor from a GHC Core one.
mkData :: DataCon -> TL.TDataCon
mkData dc = datacon
  where tyname  = mkName $ tyConName $ dataConTyCon dc
        dcname  = mkName . Var.varName $ dataConWrapId dc -- mkName $ dataConName dc
        dctag   = dataConTag dc
        args    = map mkType $ dataConOrigArgTys dc
        datacon = case fst dcname of
            "I#" -> TL.PrimCon TL.I
            "F#" -> TL.PrimCon TL.F
            "D#" -> TL.PrimCon TL.D
            "C#" -> TL.PrimCon TL.C
            "False" -> TL.PrimCon TL.DFalse
            "True"  -> TL.PrimCon TL.DTrue
            _ -> TL.DataCon dcname dctag (TL.TyConApp tyname []) args

-- | Make Type
--   Make a TL.TType given a GHC Core one.
mkType :: Type -> TL.TType
mkType (TyVarTy var)    = TL.TyVar (mkName $ tyVarName var)
mkType (AppTy t1 t2)    = TL.TyApp (mkType t1) (mkType t2)
-- mkType (FunTy t1 t2)    = TL.TyFun (mkType t1) (mkType t2)
-- mkType (ForAllTy v t)   = TL.TyForAll (mkName $ Var.varName v) (mkType t)
mkType (LitTy _)       = error "Literal types are sketchy?"
mkType (TyConApp tc kt) = case mkName . tyConName $ tc of 
    ("Int#", _)    -> TL.TyRawInt
    ("Float#", _)  -> TL.TyRawFloat
    ("Double#", _) -> TL.TyRawDouble
    ("Char#", _)   -> TL.TyRawChar
    x -> TL.TyConApp x (map mkType kt)

-- | Make Expression Environment
--   Make the expression environment given a GHC Core.
mkEEnv :: CoreProgram -> TL.TEEnv
mkEEnv binds = M.fromList $ concatMap mkBinds binds

-- | Make Bindings
--   Make TL Binding given a GHC Core binding.
mkBinds :: CoreBind -> [(TL.TName, TL.TExpr)]
mkBinds (Rec binds) = map (\(b, e) -> (mkName $ Var.varName b, mkExpr e)) binds
mkBinds (NonRec bndr expr) = [(gname, gexpr)]
  where gname = mkName $ Var.varName bndr
        gexpr = mkExpr expr

-- Catching data cons.
pdcset :: [String]
pdcset = ["I#", "F#", "D#", "C#", "True", "False"]

-- | Make Expression
--   Make a TL.TExpression from a GHC Core Expression.
mkExpr :: CoreExpr -> TL.TExpr
mkExpr (Var id)    =
    if (occNameString $ nameOccName $ Var.varName id) `elem` pdcset
        then TL.Data (mkCaughtDataCon id)
        else TL.Var (mkName $ Var.varName id) (mkType $ varType id)
mkExpr (Lit lit)   = TL.Const (mkLit lit)
mkExpr (App f a)   = TL.App (mkExpr f) (mkExpr a)
mkExpr l@(Lam b e) =
    let ge = mkExpr e
        et = G2.exprType ge
        an = mkName $ Var.varName b
    in TL.Lam an ge ((mkType . CU.exprType) l)
mkExpr (Case e b t as) =
    let ex = mkExpr e
        ty = mkType t
    in case recoverCons $ mkType (CU.exprType e) of
        -- This means that the matching expression has a data constructor that
        -- is one of the primitive types. Consequently, we must adapt the rest
        -- of the Alts in order to accommodate for this. We use cascadeAlt in
        -- order to convert every pattern match into a pattern match on Bool
        -- values as opposed to one on constructor structural isomorphism.
        Just dc -> cascadeAlt ex dc (sortAlt as)

        -- Otherwise we are free to make simplifications :)
        Nothing -> TL.App (TL.Lam (mkName $ Var.varName b)
                            (TL.Case ex (map mkAlt as) ty)
                            (TL.TyFun (mkType $ CU.exprType (Var b)) ty))
                          ex
mkExpr (Cast e c) = mkExpr e
mkExpr (Tick t e) = mkExpr e
mkExpr (Type t)   = TL.Type (mkType t)
mkExpr (Let  bs e) = TL.Let (mkBinds bs) (mkExpr e)

-- | Make Literal
--   GHC Core Literals correspond to TL Consts actually :)
mkLit :: Literal -> TL.Const
mkLit (MachChar char)  = TL.CChar char
mkLit (MachStr bytstr) = TL.CString (show bytstr)
mkLit (MachInt int)    = TL.CInt (fromInteger int)
mkLit (MachInt64 int)  = TL.CInt (fromInteger int)
mkLit (MachWord int)   = TL.CInt (fromInteger int)
mkLit (MachWord64 int) = TL.CInt (fromInteger int)
mkLit (MachFloat rat)  = TL.CFloat rat
mkLit (MachDouble rat) = TL.CDouble rat
mkLit (LitInteger i t) = TL.CInt (fromInteger i)
mkLit otherwise        = error "No other lits please?"

-- | Make Alt
--   Make TL Alt from GHC Core Alt.
mkAlt :: CoreAlt -> (TL.TAlt, TL.TExpr)
mkAlt (ac, args, exp) = (TL.Alt (mkA ac,map (mkName . Var.varName) args),g2exp)
  where g2exp = mkExpr exp
        mkA (DataAlt dc) = mkData dc
        mkA DEFAULT = TL.DEFAULT
        mkA (LitAlt lit) = case lit of
            MachChar char -> P.p_d_char
            MachStr _ -> error "Should we even have strings?"
            MachInt _ -> P.p_d_int
            MachInt64 _ -> P.p_d_int
            MachFloat _ -> P.p_d_float
            MachDouble _ -> P.p_d_double
            otherwise      -> error "Unsupported alt condition."

-- | Sort Alt
--   Propagate DEFAULT data constructors to the back. This is needed for the
--   cascadeAlt function later.
sortAlt :: [CoreAlt] -> [CoreAlt]
sortAlt [] = []
sortAlt ((ac, args, exp):as) = case ac of
    DataAlt dc -> (ac, args, exp) : sortAlt as
    LitAlt lit -> (ac, args, exp) : sortAlt as
    DEFAULT    -> sortAlt as ++ [(ac, args, exp)]

-- | Cascade Alts
--   The goal here is to convert Literal data constructors into equality case
--   matchings on Bools. Rather complicated and annoying.
--   Injection of operators from Internals.Translation.Prelude.
cascadeAlt :: TL.TExpr -> TL.TDataCon -> [CoreAlt] -> TL.TExpr
cascadeAlt _ _ [] = TL.BAD
cascadeAlt mx recon@(TL.DataCon n _ t ts) ((ac, args, exp):as) = case ac of
    DataAlt dc -> error "We should not see non-raw data consturctors here"
    DEFAULT    -> mkExpr exp
    LitAlt lit ->
        TL.Case (TL.App (TL.App (TL.App (TL.App P.op_eq
                                                (TL.Type TL.TyBottom))
                                        P.d_eq)
                                (TL.App (TL.Var n . toTyFun ts $ t) mx))
                        (TL.App (TL.Var n . toTyFun ts $ t)
                                (TL.Const (mkLit lit))))
                  [(TL.Alt (P.p_d_true, []), mkExpr exp)
                  ,(TL.Alt (P.p_d_false, []), cascadeAlt mx recon as)]
                (mkType $ CU.exprType exp)
  where toTyFun :: [TL.TType] -> TL.TType -> TL.TType
        toTyFun [] t = t
        toTyFun (t:[]) t' = TL.TyFun t t'
        toTyFun (t:ts) t' = TL.TyFun t (toTyFun ts t')

-- | Recover Primitive Data Constructors
--   Given a TL.TType, recover the corresponding data constructor that fakes the
--   primitive data constructor of GHC Core.
recoverCons :: TL.TType -> Maybe TL.TDataCon
recoverCons TL.TyRawInt = Just P.p_d_int
recoverCons TL.TyRawFloat = Just P.p_d_float
recoverCons TL.TyRawDouble = Just P.p_d_double
recoverCons TL.TyRawChar = Just P.p_d_char
recoverCons _ = Nothing

-- | Make Caught DataCon
mkCaughtDataCon :: Id -> TL.TDataCon
mkCaughtDataCon i = case occ of
    "I#"    -> TL.PrimCon TL.I
    "D#"    -> TL.PrimCon TL.D
    "F#"    -> TL.PrimCon TL.F
    "C#"    -> TL.PrimCon TL.C
    "True"  -> TL.PrimCon TL.DTrue
    "False" -> TL.PrimCon TL.DFalse
    x -> error $ "Unknown interception: " ++ x
  where occ = occNameString $ nameOccName $ Var.varName i
-}

