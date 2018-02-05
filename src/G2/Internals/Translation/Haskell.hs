{-# LANGUAGE OverloadedStrings #-}

-- | Haskell Translation
module G2.Internals.Translation.Haskell
    ( CompileClosure
    , mkCompileClosure
    , hskToG2
    , mkIOString
    , prim_list
    , rawDump
    , mkId
    , mkIdUnsafe
    , mkName
    , mkTyConName
    , mkData
    ) where

import qualified G2.Internals.Language as G2

import qualified Class as C
import Coercion
import CoreSyn
import DataCon
import DynFlags
import GHC
import GHC.Paths
import HscMain
import HscTypes
import InstEnv
import Literal
import Name
import Outputable
import Pair
import TidyPgm
import TyCon
import TyCoRep
import Unique
import Var as V

import Data.Foldable
import Data.Maybe

import qualified Outputable as Out

import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

mkIOString :: (Outputable a) => a -> IO String
mkIOString obj = runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    return (showPpr dflags obj)

mkRawCore :: FilePath -> IO CoreModule
mkRawCore fp = runGhc (Just libdir) $ do
    _ <- setSessionDynFlags =<< getSessionDynFlags
    -- compileToCoreModule fp
    compileToCoreSimplified fp

rawDump :: FilePath -> IO ()
rawDump fp = do
  core <- mkRawCore fp
  str <- mkIOString core
  putStrLn str

type NameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name
type TypeNameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name

equivMods :: HM.HashMap T.Text T.Text
equivMods = HM.fromList
            [ ("GHC.Classes2", "GHC.Classes")
            , ("GHC.Types2", "GHC.Types")
            , ("GHC.Integer2", "GHC.Integer")
            , ("GHC.Integer.Type2", "GHC.Integer.Type")
            , ("GHC.Prim2", "GHC.Prim")
            , ("GHC.Tuple2", "GHC.Tuple")
            , ("GHC.Magic2", "GHC.Magic")
            , ("GHC.CString2", "GHC.CString")
            , ("Data.Map.Base", "Data.Map")]

hskToG2 :: FilePath -> FilePath -> NameMap -> TypeNameMap -> Bool -> 
    IO (String, G2.Program, [G2.ProgramType], [(G2.Name, G2.Id, [G2.Id])], NameMap, TypeNameMap)
hskToG2 proj src nm tm simpl = do
    (mod_name, sums_gutss, _, _, c) <- mkCompileClosure proj src simpl
    
    let (nm2, binds) = mapAccumR (\nm' (_, _, b) -> mapAccumR (\v -> mkBinds v tm) nm' b) nm sums_gutss
    let binds' = concat binds

    let ((nm3, tm2), tycons) = mapAccumR (\(nm', tm') (_, t, _) -> mapAccumR (uncurry mkTyCon) (nm', tm') t) (nm2, tm) sums_gutss
    let tycons' = concat tycons

    let classes = map (mkClass tm2) c
    return (mod_name, binds', tycons', classes, nm3, tm2)

type CompileClosure = (String, [(ModSummary, [TyCon], [CoreBind])], DynFlags, HscEnv, [ClsInst])

mkCompileClosure :: FilePath -> FilePath -> Bool -> IO CompileClosure
mkCompileClosure proj src simpl = do
    (mod_graph, mod_gutss, dflags, env) <- runGhc (Just libdir) $ do
        beta_flags <- getSessionDynFlags
        let gen_flags = []
        -- let gen_flags = [ Opt_CmmSink
        --                 , Opt_SimplPreInlining
        --                 , Opt_DoEtaReduction
        --                 , Opt_IgnoreInterfacePragmas]
        let beta_flags' = foldl' gopt_unset beta_flags gen_flags
        let dflags = beta_flags' { importPaths = [proj]
                                 , ufCreationThreshold = if simpl then ufCreationThreshold beta_flags' else -1000
                                 , ufUseThreshold = if simpl then ufUseThreshold beta_flags' else -1000
                                 , ufFunAppDiscount = if simpl then ufFunAppDiscount beta_flags' else -1000
                                 , ufDictDiscount = if simpl then ufDictDiscount beta_flags' else -1000
                                 , ufKeenessFactor = if simpl then ufKeenessFactor beta_flags' else -1000}
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
        return (mod_graph, mod_gutss, dflags, env)

    -- Perform simplification and tidying, which is necessary for getting the
    -- typeclass selector functions.
    smpl_gutss <- mapM (hscSimplify env) mod_gutss
    tidy_pgms <- mapM (tidyProgram env) smpl_gutss-- (if simpl then smpl_gutss else mod_gutss)
    let cg_gutss = map fst tidy_pgms
    let tcss_pgms = map (\c -> (cg_tycons c, cg_binds c)) cg_gutss
    let (tcss, bindss) = unzip tcss_pgms

    -- Get TypeClasses
    let cls_insts = concatMap mg_insts mod_gutss

    let mod_name = moduleNameString $ moduleName $ ms_mod $ head mod_graph

    return (mod_name, zip3 mod_graph tcss bindss, dflags, env, cls_insts)
    -- return (zip3 mod_graph (map mg_tcs mod_gutss) (map mg_binds mod_gutss), dflags, env)

mkBinds :: NameMap -> TypeNameMap -> CoreBind -> (NameMap, [(G2.Id, G2.Expr)])
mkBinds nm tm (NonRec var expr) = 
    let
        (i, nm') = mkIdUpdatingNM var nm tm
    in
    (nm', [(i, mkExpr nm' tm expr)])
mkBinds nm tm (Rec ves) =
    mapAccumR (\nm' (v, e) ->
                let
                    (i, nm'') = mkIdUpdatingNM v nm' tm
                in
                (nm'', (i, mkExpr nm'' tm e))
            ) nm ves

mkExpr :: NameMap  -> TypeNameMap -> CoreExpr -> G2.Expr
mkExpr nm tm (Var var) = G2.Var (mkIdLookup var nm tm)
mkExpr _ _ (Lit lit) = G2.Lit (mkLit lit)
mkExpr nm tm (App fxpr axpr) = G2.App (mkExpr nm tm fxpr) (mkExpr nm tm axpr)
mkExpr nm tm (Lam var expr) = G2.Lam (mkId tm var) (mkExpr nm tm expr)
mkExpr nm tm (Let bnd expr) = G2.Let (mkBind nm tm bnd) (mkExpr nm tm expr)
mkExpr nm tm (Case mxpr var _ alts) = G2.Case (mkExpr nm tm mxpr) (mkId tm var) (mkAlts nm tm alts)
mkExpr nm tm (Cast expr c) =  G2.Cast (mkExpr nm tm expr) (mkCoercion tm c)
mkExpr _  tm (Coercion c) = G2.Coercion (mkCoercion tm c)
mkExpr nm tm (Tick _ expr) = mkExpr nm tm expr
mkExpr _ tm (Type ty) = G2.Type (mkType tm ty)

mkId :: TypeNameMap -> Id -> G2.Id
mkId tm vid = G2.Id ((mkName . V.varName) vid) ((mkType tm . varType) vid)

-- Makes an Id, not respecting UniqueIds
mkIdUnsafe :: Id -> G2.Id
mkIdUnsafe vid = G2.Id ((mkName . V.varName) vid) (mkType HM.empty . varType $ vid)

mkIdLookup :: Id -> NameMap -> TypeNameMap -> G2.Id
mkIdLookup i nm tm =
    let
        n = mkNameLookup (V.varName i) nm
        t = mkType tm . varType $ i
    in
    G2.Id n t

mkIdUpdatingNM :: Id -> NameMap -> TypeNameMap -> (G2.Id, NameMap)
mkIdUpdatingNM vid nm tm =
    let
        n@(G2.Name n' m _) = mkName . V.varName $ vid
        i = G2.Id n ((mkType tm . varType) vid)

        nm' = HM.insert (n', m) n nm
    in
    (i, nm')

mkName :: Name -> G2.Name
mkName name = G2.Name occ mdl unq
  where
    occ = T.pack . occNameString . nameOccName $ name
    unq = (getKey . nameUnique) name
    mdl = case nameModule_maybe name of
              Nothing -> Nothing
              Just md -> switchModule (T.pack . moduleNameString . moduleName $ md)

mkNameLookup :: Name -> NameMap -> G2.Name
mkNameLookup name nm =
    -- We only lookup in the NameMap if the Module name is not Nothing
    -- Internally, a module may use multiple variables with the same name and a module Nothing
    case mdl of
        Nothing -> G2.Name occ mdl unq
        _ -> case HM.lookup (occ, mdl) nm of
                Just n' -> n'
                Nothing -> G2.Name occ mdl unq
    where
        occ = T.pack . occNameString . nameOccName $ name
        unq = getKey . nameUnique $ name
        mdl = case nameModule_maybe name of
                  Nothing -> Nothing
                  Just md -> switchModule (T.pack . moduleNameString . moduleName $ md)

switchModule :: T.Text -> Maybe T.Text
switchModule m =
    case HM.lookup m equivMods of
        Just m'' -> Just m''
        Nothing -> Just m

mkLit :: Literal -> G2.Lit
mkLit (MachChar chr) = G2.LitChar chr
mkLit (MachStr bstr) = G2.LitString (show bstr)
mkLit (MachInt i) = G2.LitInt (fromInteger i)
mkLit (MachInt64 i) = G2.LitInt (fromInteger i)
mkLit (MachWord i) = G2.LitInt (fromInteger i)
mkLit (MachWord64 i) = G2.LitInt (fromInteger i)
mkLit (MachFloat rat) = G2.LitFloat rat
mkLit (MachDouble rat) = G2.LitDouble rat
mkLit (LitInteger i _) = G2.LitInteger (fromInteger i)
mkLit (MachNullAddr) = error "mkLit: MachNullAddr"
mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: NameMap -> TypeNameMap -> CoreBind -> [(G2.Id, G2.Expr)]
mkBind nm tm (NonRec var expr) = [(mkId tm var, mkExpr nm tm expr)]
mkBind nm tm (Rec ves) = map (\(v, e) -> (mkId tm v, mkExpr nm tm e)) ves

mkAlts :: NameMap -> TypeNameMap -> [CoreAlt] -> [G2.Alt]
mkAlts nm tm = map (mkAlt nm tm)

mkAlt :: NameMap -> TypeNameMap -> CoreAlt -> G2.Alt
mkAlt nm tm (acon, prms, expr) = G2.Alt (mkAltMatch nm tm acon prms) (mkExpr nm tm expr)

mkAltMatch :: NameMap -> TypeNameMap -> AltCon -> [Var] -> G2.AltMatch
mkAltMatch nm tm (DataAlt dcon) params = G2.DataAlt (mkData nm tm dcon) (map (mkId tm) params)
mkAltMatch _ _ (LitAlt lit) _ = G2.LitAlt (mkLit lit)
mkAltMatch _ _ (DEFAULT) _ = G2.Default

mkType :: TypeNameMap -> Type -> G2.Type
mkType tm (TyVarTy v) = G2.TyVar $ mkId tm v-- (mkName (V.varName v)) (mkType (varType v))
mkType tm (AppTy t1 t2) = G2.TyApp (mkType tm t1) (mkType tm t2)
mkType tm (ForAllTy (Anon t) ty) = G2.TyFun (mkType tm t) (mkType tm ty)
mkType tm (ForAllTy b ty) = G2.TyForAll (mkTyBinder tm b) (mkType tm ty)
mkType tm (LitTy _) = G2.TyBottom
mkType tm (CastTy _ _) = error "mkType: CastTy"
mkType tm (CoercionTy _) = error "mkType: Coercion"
mkType tm (TyConApp tc ts) = if not (isFunTyCon tc) || (length ts /= 2)
    then G2.TyConApp (mkTyConName tm tc) (map (mkType tm) ts)
    else case ts of
        (t1:t2:[]) -> G2.TyFun (mkType tm t1) (mkType tm t2)
        _ -> error "mkType: non-arity 2 FunTyCon from GHC"

mkTyCon :: NameMap -> TypeNameMap -> TyCon -> ((NameMap, TypeNameMap), G2.ProgramType)
mkTyCon nm tm t = ((nm', tm'), (n, dcs))
  where
    n@(G2.Name n' m _) = mkName . tyConName $ t
    tm' = HM.insert (n', m) n tm

    nm' = foldr (uncurry HM.insert) nm
            $ map (\n_@(G2.Name n'_ m_ _) -> ((n'_, m_), n_)) 
            $ map (flip mkNameLookup nm . dataConName) $ visibleDataCons (algTyConRhs t)

    bv = map (mkName . V.varName) $ tyConTyVars t

    dcs = 
        case algTyConRhs t of
            DataTyCon { data_cons = dc } -> G2.DataTyCon bv $ map (mkData nm' tm) dc
            NewTyCon { data_con = dc
                     , nt_rhs = t} -> G2.NewTyCon { G2.bound_names = bv
                                                  , G2.data_con = mkData nm' tm dc
                                                  , G2.rep_type = mkType tm t}
    -- dcs = if isDataTyCon t then map mkData . data_cons . algTyConRhs $ t else []

mkTyConName :: TypeNameMap -> TyCon -> G2.Name
mkTyConName tm tc =
    let
        n@(G2.Name n' m _) = mkName $ tyConName tc
    in
    case HM.lookup (n', m) tm of
    Just tn -> tn
    Nothing -> n

mkData :: NameMap -> TypeNameMap -> DataCon -> G2.DataCon
mkData nm tm datacon = G2.DataCon name ty tys
  where
    name = mkDataName nm datacon
    ty = (mkType tm . dataConRepType) datacon
    tys  = map (mkType tm) (dataConOrigArgTys datacon)

mkDataName :: NameMap -> DataCon -> G2.Name
mkDataName nm datacon = (flip mkNameLookup nm . dataConName) datacon

mkTyBinder :: TypeNameMap -> TyBinder -> G2.TyBinder
mkTyBinder tm (Anon t) = G2.AnonTyBndr (mkType tm t)
mkTyBinder tm (Named v _) = G2.NamedTyBndr (mkId tm v)

prim_list :: [String]
prim_list = [">=", ">", "==", "/=", "<=", "<",
             "&&", "||", "not",
             "+", "-", "*", "/", "implies", "negate", "error", "iff" ]


mkCoercion :: TypeNameMap -> Coercion -> G2.Coercion
mkCoercion tm c =
    let
        k = fmap (mkType tm) $ coercionKind c
    in
    (pFst k) G2.:~ (pSnd k)

mkClass :: TypeNameMap -> ClsInst -> (G2.Name, G2.Id, [G2.Id])
mkClass tm (ClsInst { is_cls = c, is_dfun = dfun, is_tcs = tcs, is_tvs = tvs, is_tys = tys }) = 
    (flip mkNameLookup tm . C.className $ c, mkId tm dfun, map (mkId tm) $ C.classTyVars c)
