{-# LANGUAGE OverloadedStrings #-}

-- | Haskell Translation
module G2.Translation.Haskell
    ( loadProj
    , hskToG2ViaModGuts
    , hskToG2ViaModGutsFromFile
    , hskToG2ViaCgGuts
    , hskToG2ViaCgGutsFromFile
    , mkCgGutsClosure
    , mkModDetailsClosure
    , mergeExtractedG2s
    , mkIOString
    , prim_list
    , rawDump
    , mkId
    , mkIdUnsafe
    , mkName
    , mkTyConName
    , mkData
    , mkSpan
    , mkRealSpan
    , absVarLoc
    , readFileExtractedG2
    , readAllExtractedG2s
    , mergeFileExtractedG2s
    ) where

import qualified G2.Language.TypeEnv as G2 (AlgDataTy (..), ProgramType)
import qualified G2.Language.Syntax as G2
-- import qualified G2.Language.Typing as G2
import qualified G2.Translation.TransTypes as G2

import Avail
import qualified Class as C
import Coercion
import CoreSyn
import DataCon
import DynFlags
import FastString
import GHC
import GHC.Paths
import HscMain
import HscTypes
import InstEnv
import Literal
import Name
import Outputable
import Pair
import SrcLoc
import TidyPgm
import TyCon
import TyCoRep
import Unique
import Var as V

import qualified Data.Array as A
import qualified Data.ByteString.Char8 as C
import Data.Foldable
import Data.List
import Data.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T
import System.Directory


-- Copying from Language.Typing so the thing we stuff into Ghc
-- does not have to rely on Language.Typing, which depends on other things.
mkG2TyApp :: [G2.Type] -> G2.Type
mkG2TyApp [] = G2.TYPE
mkG2TyApp (t:[]) = t
mkG2TyApp (t1:t2:ts) = mkG2TyApp (G2.TyApp t1 t2 : ts)

mkG2TyCon :: G2.Name
        -> [G2.Type]
        -> G2.Kind
        -> G2.Type
mkG2TyCon n ts k = mkG2TyApp $ G2.TyCon n k:ts


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


loadProj ::  Maybe HscTarget -> FilePath -> FilePath -> [GeneralFlag] -> Bool -> Ghc SuccessFlag
loadProj hsc proj src gflags simpl = do
    beta_flags <- getSessionDynFlags
    let gen_flags = gflags

    let init_beta_flags = gopt_unset beta_flags Opt_StaticArgumentTransformation

    let beta_flags' = foldl' gopt_set init_beta_flags gen_flags
    let dflags = beta_flags' { hscTarget = case hsc of
                                                Just hsc' -> hsc'
                                                _ -> hscTarget beta_flags'
                             , includePaths = includePaths beta_flags'
                             , importPaths = [proj]

                             , simplPhases = if simpl then simplPhases beta_flags' else 0
                             , maxSimplIterations = if simpl then maxSimplIterations beta_flags' else 0

                             , hpcDir = proj}

    

    _ <- setSessionDynFlags dflags
    target <- guessTarget src Nothing
    _ <- setTargets [target]
    load LoadAllTargets



-- Compilation pipeline with CgGuts
hskToG2ViaCgGutsFromFile :: Maybe HscTarget -> FilePath -> FilePath -> G2.NameMap -> G2.TypeNameMap -> Bool -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaCgGutsFromFile hsc proj src nm tm simpl = do
  closures <-mkCgGutsModDetailsClosuresFromFile hsc proj src simpl
  return $ hskToG2ViaCgGuts nm tm closures


hskToG2ViaCgGuts :: G2.NameMap -> G2.TypeNameMap -> [(G2.CgGutsClosure, G2.ModDetailsClosure)]
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaCgGuts nm tm pairs = do
  let (nm2, tm2, exg2s) = foldr (\(c, m) (nm', tm', exs) ->
                            let mgcc = cgGutsModDetailsClosureToModGutsClosure c m in
                            let (nm'', tm'', g2) = modGutsClosureToG2 nm' tm' mgcc in
                              (nm'', tm'', g2 : exs))
                            (nm, tm, [])
                            pairs in
    (nm2, tm2, mergeExtractedG2s exg2s)


cgGutsModDetailsClosureToModGutsClosure :: G2.CgGutsClosure -> G2.ModDetailsClosure -> G2.ModGutsClosure
cgGutsModDetailsClosureToModGutsClosure cg md =
  G2.ModGutsClosure
    { G2.mgcc_mod_name = G2.cgcc_mod_name cg
    , G2.mgcc_binds = G2.cgcc_binds cg
    , G2.mgcc_tycons = G2.cgcc_tycons cg
    , G2.mgcc_breaks = G2.cgcc_breaks cg
    , G2.mgcc_cls_insts = G2.mdcc_cls_insts md
    , G2.mgcc_type_env = G2.mdcc_type_env md
    , G2.mgcc_exports = G2.mdcc_exports md
    , G2.mgcc_deps = G2.mdcc_deps md
    }


mkCgGutsModDetailsClosuresFromFile :: Maybe HscTarget -> FilePath -> FilePath -> Bool 
  -> IO [(G2.CgGutsClosure, G2.ModDetailsClosure)]
mkCgGutsModDetailsClosuresFromFile hsc proj src simpl = do
  (env, modgutss) <- runGhc (Just libdir) $ do
      _ <- loadProj hsc proj src [] simpl
      env <- getSession

      mod_graph <- getModuleGraph
      parsed_mods <- mapM parseModule mod_graph
      typed_mods <- mapM typecheckModule parsed_mods
      desug_mods <- mapM desugarModule typed_mods
      return (env, map coreModule desug_mods)

  simplgutss <- mapM (if simpl then hscSimplify env else return . id) modgutss
  tidys <- mapM (tidyProgram env) simplgutss
  let pairs = map (\((cg, md), mg) -> (mkCgGutsClosure cg, mkModDetailsClosure (mg_deps mg) md)) $ zip tidys simplgutss
  return pairs


mkCgGutsClosure :: CgGuts -> G2.CgGutsClosure
mkCgGutsClosure cgguts =
  G2.CgGutsClosure
    { G2.cgcc_mod_name = Just $ moduleNameString $ moduleName $ cg_module cgguts
    , G2.cgcc_binds = cg_binds cgguts
    , G2.cgcc_breaks = cg_modBreaks cgguts
    , G2.cgcc_tycons = cg_tycons cgguts }


mkModDetailsClosure :: Dependencies -> ModDetails -> G2.ModDetailsClosure
mkModDetailsClosure deps moddet =
  G2.ModDetailsClosure
    { G2.mdcc_cls_insts = md_insts moddet
    , G2.mdcc_type_env = md_types moddet
    , G2.mdcc_exports = exportedNames moddet
    , G2.mdcc_deps = map (moduleNameString . fst) $ dep_mods deps
    }



-- Compilation pipeline with ModGuts
hskToG2ViaModGutsFromFile :: Maybe HscTarget -> FilePath -> FilePath -> G2.NameMap -> G2.TypeNameMap -> Bool -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaModGutsFromFile hsc proj src nm tm simpl = do
  closures <- mkModGutsClosuresFromFile hsc proj src simpl
  return $ hskToG2ViaModGuts nm tm closures
   

hskToG2ViaModGuts :: G2.NameMap -> G2.TypeNameMap -> [G2.ModGutsClosure]
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaModGuts nm tm modgutss =
  let (nm2, tm2, exg2s) = foldr (\m (nm', tm', cls) ->
                                let (nm'', tm'', mc) = modGutsClosureToG2 nm' tm' m in
                                  (nm'', tm'', mc : cls))
                                (nm, tm, [])
                                modgutss in
    (nm2, tm2, mergeExtractedG2s exg2s)




modGutsClosureToG2 :: G2.NameMap -> G2.TypeNameMap -> G2.ModGutsClosure
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
modGutsClosureToG2 nm tm mgcc =
  let breaks = G2.mgcc_breaks mgcc in
  -- Do the binds
  let (nm2, binds) = foldr (\b (nm', bs) ->
                              let (nm'', bs') = mkBinds nm' tm breaks b in
                                (nm'', bs ++ bs'))
                           (nm, [])
                           (G2.mgcc_binds mgcc) in
  -- Do the tycons
  let raw_tycons = G2.mgcc_tycons mgcc ++ typeEnvTyCons (G2.mgcc_type_env mgcc) in
  let (nm3, tm2, tycons) = foldr (\tc (nm', tm', tcs) ->
                                  let ((nm'', tm''), mb_t) = mkTyCon nm' tm' tc in
                                    (nm'', tm'', maybeToList mb_t ++ tcs))
                                (nm2, tm, [])
                                raw_tycons in
  -- Do the class
  let classes = map (mkClass tm2) $ G2.mgcc_cls_insts mgcc in

  -- Do the exports
  let exports = G2.mgcc_exports mgcc in
  let deps = fmap T.pack $ G2.mgcc_deps mgcc in
    (nm3, tm2,
        G2.ExtractedG2
          { G2.exg2_mod_names = maybeToList $ fmap T.pack $ G2.mgcc_mod_name mgcc
          , G2.exg2_binds = binds
          , G2.exg2_tycons = tycons
          , G2.exg2_classes = classes
          , G2.exg2_exports = exports
          , G2.exg2_deps = deps })
  

mkModGutsClosuresFromFile :: Maybe HscTarget -> FilePath -> FilePath -> Bool -> IO [G2.ModGutsClosure]
mkModGutsClosuresFromFile hsc proj src simpl = do
  (env, modgutss) <- runGhc (Just libdir) $ do
      _ <- loadProj hsc proj src [] simpl
      env <- getSession

      mod_graph <- getModuleGraph
      parsed_mods <- mapM parseModule mod_graph
      typed_mods <- mapM typecheckModule parsed_mods
      desug_mods <- mapM desugarModule typed_mods
      return (env, map coreModule desug_mods)

  if simpl then do
    simpls <- mapM (hscSimplify env) modgutss
    closures <- mapM (mkModGutsClosure env) simpls
    return closures
  else do
    closures <- mapM (mkModGutsClosure env) modgutss
    return closures

-- This one will need to do the Tidy program stuff
mkModGutsClosure :: HscEnv -> ModGuts -> IO G2.ModGutsClosure
mkModGutsClosure env modguts = do
  (cgguts, moddets) <- tidyProgram env modguts
  return
    G2.ModGutsClosure
      { G2.mgcc_mod_name = Just $ moduleNameString $ moduleName $ cg_module cgguts
      , G2.mgcc_binds = cg_binds cgguts
      , G2.mgcc_tycons = cg_tycons cgguts
      , G2.mgcc_breaks = cg_modBreaks cgguts
      , G2.mgcc_cls_insts = md_insts moddets
      , G2.mgcc_type_env = md_types moddets
      , G2.mgcc_exports = exportedNames moddets
      , G2.mgcc_deps = map (moduleNameString . fst) $ dep_mods $ mg_deps modguts
      }


-- Merging, order matters!
mergeExtractedG2s :: [G2.ExtractedG2] -> G2.ExtractedG2
mergeExtractedG2s [] = G2.emptyExtractedG2
mergeExtractedG2s (g2:g2s) =
  let g2' = mergeExtractedG2s g2s in
    G2.ExtractedG2
      { G2.exg2_mod_names = G2.exg2_mod_names g2 ++ G2.exg2_mod_names g2' -- order matters
      , G2.exg2_binds = G2.exg2_binds g2 ++ G2.exg2_binds g2'
      , G2.exg2_tycons = G2.exg2_tycons g2 ++ G2.exg2_tycons g2'
      , G2.exg2_classes = G2.exg2_classes g2 ++ G2.exg2_classes g2'
      , G2.exg2_exports = G2.exg2_exports g2 ++ G2.exg2_exports g2'
      , G2.exg2_deps = G2.exg2_deps g2 ++ G2.exg2_deps g2' }

----------------
-- Translating the individual components in CoreSyn, etc into G2 Core

mkBinds :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreBind -> (G2.NameMap, [(G2.Id, G2.Expr)])
mkBinds nm tm mb (NonRec var expr) = 
    let
        (i, nm') = mkIdUpdatingNM var nm tm
    in
    (nm', [(i, mkExpr nm' tm mb expr)])
mkBinds nm tm mb (Rec ves) =
    mapAccumR (\nm' (v, e) ->
                let
                    (i, nm'') = mkIdUpdatingNM v nm' tm
                in
                (nm'', (i, mkExpr nm'' tm mb e))
            ) nm ves

mkExpr :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreExpr -> G2.Expr
mkExpr nm tm _ (Var var) = G2.Var (mkIdLookup var nm tm)
mkExpr _ _ _ (Lit lit) = G2.Lit (mkLit lit)
mkExpr nm tm mb (App fxpr axpr) = G2.App (mkExpr nm tm mb fxpr) (mkExpr nm tm mb axpr)
mkExpr nm tm mb (Lam var expr) = G2.Lam (mkLamUse var) (mkId tm var) (mkExpr nm tm mb expr)
mkExpr nm tm mb (Let bnd expr) = G2.Let (mkBind nm tm mb bnd) (mkExpr nm tm mb expr)
mkExpr nm tm mb (Case mxpr var _ alts) = G2.Case (mkExpr nm tm mb mxpr) (mkId tm var) (mkAlts nm tm mb alts)
mkExpr nm tm mb (Cast expr c) =  G2.Cast (mkExpr nm tm mb expr) (mkCoercion tm c)
mkExpr _  tm _ (Coercion c) = G2.Coercion (mkCoercion tm c)
mkExpr nm tm mb (Tick t expr) =
    case createTickish mb t of
        Just t' -> G2.Tick t' $ mkExpr nm tm mb expr
        Nothing -> mkExpr nm tm mb expr
mkExpr _ tm _ (Type ty) = G2.Type (mkType tm ty)

createTickish :: Maybe ModBreaks -> Tickish i -> Maybe G2.Tickish
createTickish (Just mb) (Breakpoint {breakpointId = bid}) =
    case mkSpan $ modBreaks_locs mb A.! bid of
        Just s -> Just $ G2.Breakpoint $ s
        Nothing -> Nothing
createTickish _ _ = Nothing

mkLamUse :: Id -> G2.LamUse
mkLamUse v
    | isTyVar v = G2.TypeL
    | otherwise = G2.TermL

mkId :: G2.TypeNameMap -> Id -> G2.Id
mkId tm vid = G2.Id ((mkName . V.varName) vid) ((mkType tm . varType) vid)

-- Makes an Id, not respecting UniqueIds
mkIdUnsafe :: Id -> G2.Id
mkIdUnsafe vid = G2.Id ((mkName . V.varName) vid) (mkType HM.empty . varType $ vid)

mkIdLookup :: Id -> G2.NameMap -> G2.TypeNameMap -> G2.Id
mkIdLookup i nm tm =
    let
        n = mkNameLookup (V.varName i) nm
        t = mkType tm . varType $ i
    in
    G2.Id n t

mkIdUpdatingNM :: Id -> G2.NameMap -> G2.TypeNameMap -> (G2.Id, G2.NameMap)
mkIdUpdatingNM vid nm tm =
    let
        n@(G2.Name n' m _ _) = mkName . V.varName $ vid
        i = G2.Id n ((mkType tm . varType) vid)

        nm' = HM.insert (n', m) n nm
    in
    (i, nm')

mkName :: Name -> G2.Name
mkName name = G2.Name occ mdl unq sp
  where
    occ = T.pack . occNameString . nameOccName $ name
    unq = (getKey . nameUnique) name
    mdl = case nameModule_maybe name of
              Nothing -> Nothing
              Just md -> switchModule (T.pack . moduleNameString . moduleName $ md)

    sp = mkSpan $ getSrcSpan name

mkNameLookup :: Name -> G2.NameMap -> G2.Name
mkNameLookup name nm =
    -- We only lookup in the G2.NameMap if the Module name is not Nothing
    -- Internally, a module may use multiple variables with the same name and a module Nothing
    case mdl of
        Nothing -> G2.Name occ mdl unq sp
        _ -> case HM.lookup (occ, mdl) nm of
                Just (G2.Name n' m i _) -> G2.Name n' m i sp
                Nothing -> G2.Name occ mdl unq sp
    where
        occ = T.pack . occNameString . nameOccName $ name
        unq = getKey . nameUnique $ name
        mdl = case nameModule_maybe name of
                  Nothing -> Nothing
                  Just md -> switchModule (T.pack . moduleNameString . moduleName $ md)

        sp = mkSpan $ getSrcSpan name

mkSpan :: SrcSpan -> Maybe G2.Span
mkSpan (RealSrcSpan s) = Just $ mkRealSpan s
mkSpan _ = Nothing

mkRealSpan :: RealSrcSpan -> G2.Span
mkRealSpan s =
    let
        st = mkRealLoc $ realSrcSpanStart s
        en = mkRealLoc $ realSrcSpanEnd s
    in
    G2.Span { G2.start = st
            , G2.end = en}

mkRealLoc :: RealSrcLoc -> G2.Loc
mkRealLoc l =
    G2.Loc { G2.line = srcLocLine l
           , G2.col = srcLocCol l
           , G2.file = unpackFS $ srcLocFile l}

switchModule :: T.Text -> Maybe T.Text
switchModule m =
    case HM.lookup m equivMods of
        Just m'' -> Just m''
        Nothing -> Just m

mkLit :: Literal -> G2.Lit
mkLit (MachChar chr) = G2.LitChar chr
mkLit (MachStr bstr) = G2.LitString (C.unpack bstr)
mkLit (MachInt i) = G2.LitInt (fromInteger i)
mkLit (MachInt64 i) = G2.LitInt (fromInteger i)
mkLit (MachWord i) = G2.LitInt (fromInteger i)
mkLit (MachWord64 i) = G2.LitInt (fromInteger i)
mkLit (MachFloat rat) = G2.LitFloat rat
mkLit (MachDouble rat) = G2.LitDouble rat
mkLit (LitInteger i _) = G2.LitInteger (fromInteger i)
mkLit _ = G2.LitInt 0
-- mkLit (MachNullAddr) = error "mkLit: MachNullAddr"
-- mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreBind -> [(G2.Id, G2.Expr)]
mkBind nm tm mb (NonRec var expr) = [(mkId tm var, mkExpr nm tm mb expr)]
mkBind nm tm mb (Rec ves) = map (\(v, e) -> (mkId tm v, mkExpr nm tm mb e)) ves

mkAlts :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> [CoreAlt] -> [G2.Alt]
mkAlts nm tm mb = map (mkAlt nm tm mb)

mkAlt :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreAlt -> G2.Alt
mkAlt nm tm mb (acon, prms, expr) = G2.Alt (mkAltMatch nm tm acon prms) (mkExpr nm tm mb expr)

mkAltMatch :: G2.NameMap -> G2.TypeNameMap -> AltCon -> [Var] -> G2.AltMatch
mkAltMatch nm tm (DataAlt dcon) params = G2.DataAlt (mkData nm tm dcon) (map (mkId tm) params)
mkAltMatch _ _ (LitAlt lit) _ = G2.LitAlt (mkLit lit)
mkAltMatch _ _ (DEFAULT) _ = G2.Default

mkType :: G2.TypeNameMap -> Type -> G2.Type
mkType tm (TyVarTy v) = G2.TyVar $ mkId tm v
mkType tm (AppTy t1 t2) = G2.TyApp (mkType tm t1) (mkType tm t2)
mkType tm (FunTy t1 t2) = G2.TyFun (mkType tm t1) (mkType tm t2)
mkType tm (ForAllTy b ty) = G2.TyForAll (mkTyBinder tm b) (mkType tm ty)
mkType _ (LitTy _) = G2.TyBottom
-- mkType _ (CastTy _ _) = error "mkType: CastTy"
mkType _ (CastTy _ _) = G2.TyUnknown
mkType _ (CoercionTy _) = G2.TyUnknown
-- mkType _ (CoercionTy _) = error "mkType: Coercion"
mkType tm (TyConApp tc ts)
    | isFunTyCon tc
    , length ts == 2 =
        case ts of
            (t1:t2:[]) -> G2.TyFun (mkType tm t1) (mkType tm t2)
            _ -> error "mkType: non-arity 2 FunTyCon from GHC"
    | G2.Name n _ _ _ <- mkName $ tyConName tc
    , n == "TYPE" = G2.TYPE
    | otherwise = mkG2TyCon (mkTyConName tm tc) (map (mkType tm) ts) (mkType tm $ tyConKind tc) 

mkTyCon :: G2.NameMap -> G2.TypeNameMap -> TyCon -> ((G2.NameMap, G2.TypeNameMap), Maybe G2.ProgramType)
mkTyCon nm tm t = case dcs of
                        Just dcs' -> ((nm'', tm''), Just (n, dcs'))
                        Nothing -> ((nm'', tm''), Nothing)
  where
    n@(G2.Name n' m _ _) = mkName . tyConName $ t
    tm' = HM.insert (n', m) n tm

    nm' = foldr (uncurry HM.insert) nm
            $ map (\n_@(G2.Name n'_ m_ _ _) -> ((n'_, m_), n_)) 
            $ map (flip mkNameLookup nm . dataConName) $ visibleDataCons (algTyConRhs t)

    bv = map (mkId tm) $ tyConTyVars t

    (nm'', tm'', dcs, dcsf) =
        case isAlgTyCon t of 
            True -> case algTyConRhs t of
                            DataTyCon { data_cons = dc } -> 
                                ( nm'
                                , tm'
                                , Just $ G2.DataTyCon bv $ map (mkData nm' tm) dc
                                , Just $ map (mkId tm'' . dataConWorkId) dc)
                            NewTyCon { data_con = dc
                                     , nt_rhs = rhst} -> 
                                     ( nm'
                                     , tm'
                                     , Just $ G2.NewTyCon { G2.bound_ids = bv
                                                          , G2.data_con = mkData nm' tm dc
                                                          , G2.rep_type = mkType tm rhst}
                                     , Just $ [(mkId tm'' . dataConWorkId) dc])
                            AbstractTyCon {} -> error "Unhandled TyCon AbstractTyCon"
                            -- TupleTyCon {} -> error "Unhandled TyCon TupleTyCon"
                            TupleTyCon { data_con = dc, tup_sort = ts } ->
                              ( nm'
                              , tm'
                              , Just $ G2.DataTyCon bv $ [mkData nm' tm dc]
                              , Nothing)
                            SumTyCon {} -> error "Unhandled TyCon SumTyCon"
            False -> case isTypeSynonymTyCon t of
                    True -> 
                        let
                            (tv, st) = fromJust $ synTyConDefn_maybe t
                            st' = mkType tm st
                            tv' = map (mkId tm) tv
                        in
                        (nm, tm', Just $ G2.TypeSynonym { G2.bound_ids = tv'
                                                        , G2.synonym_of = st'}, Nothing)
                    False -> (nm, tm, Nothing, Nothing)
    -- dcs = if isDataTyCon t then map mkData . data_cons . algTyConRhs $ t else []

mkTyConName :: G2.TypeNameMap -> TyCon -> G2.Name
mkTyConName tm tc =
    let
        n@(G2.Name n' m _ l) = mkName $ tyConName tc
    in
    case HM.lookup (n', m) tm of
    Just (G2.Name n'' m' i _) -> G2.Name n'' m' i l
    Nothing -> n

mkData :: G2.NameMap -> G2.TypeNameMap -> DataCon -> G2.DataCon
mkData nm tm datacon = G2.DataCon name ty
  where
    name = mkDataName nm datacon
    ty = (mkType tm . dataConRepType) datacon

mkDataName :: G2.NameMap -> DataCon -> G2.Name
mkDataName nm datacon = (flip mkNameLookup nm . dataConName) datacon

mkTyBinder :: G2.TypeNameMap -> TyVarBinder -> G2.TyBinder
mkTyBinder tm (TvBndr v _) = G2.NamedTyBndr (mkId tm v)
prim_list :: [String]
prim_list = [">=", ">", "==", "/=", "<=", "<",
             "&&", "||", "not",
             "+", "-", "*", "/", "implies", "negate", "error", "iff" ]


mkCoercion :: G2.TypeNameMap -> Coercion -> G2.Coercion
mkCoercion tm c =
    let
        k = fmap (mkType tm) $ coercionKind c
    in
    (pFst k) G2.:~ (pSnd k)

mkClass :: G2.TypeNameMap -> ClsInst -> (G2.Name, G2.Id, [G2.Id])
mkClass tm (ClsInst { is_cls = c, is_dfun = dfun }) = 
    (flip mkNameLookup tm . C.className $ c, mkId tm dfun, map (mkId tm) $ C.classTyVars c)


exportedNames :: ModDetails -> [G2.ExportedName]
exportedNames = concatMap availInfoNames . md_exports

availInfoNames :: AvailInfo -> [G2.ExportedName]
availInfoNames (Avail n) = [mkName n]
availInfoNames (AvailTC n ns _) = mkName n:map mkName ns

-- | absVarLoc'
-- Switches all file paths in Var namesand Ticks to be absolute
absVarLoc :: G2.Program -> IO G2.Program
absVarLoc = 
    mapM 
        (mapM (\(i, e) -> do 
                    e' <- absVarLoc' e
                    return (i, e')
              )
        )

absVarLoc' :: G2.Expr -> IO G2.Expr
absVarLoc' (G2.Var (G2.Id (G2.Name n m i (Just s)) t)) = do
    return $ G2.Var $ G2.Id (G2.Name n m i (Just $ s)) t
absVarLoc' (G2.App e1 e2) = do
    e1' <- absVarLoc' e1
    e2' <- absVarLoc' e2
    return $ G2.App e1' e2'
absVarLoc' (G2.Lam u i e) = return . G2.Lam u i =<< absVarLoc' e
absVarLoc' (G2.Let b e) = do
    b' <- mapM (\(i, be) -> do
                    be' <- absVarLoc' be
                    return (i, be')
               ) b
    e' <- absVarLoc' e
    return $ G2.Let b' e'
absVarLoc' (G2.Case e i as) = do
    e' <- absVarLoc' e
    as' <- mapM (\(G2.Alt a ae) -> return . G2.Alt a =<< absVarLoc' ae) as
    return $ G2.Case e' i as'
absVarLoc' (G2.Cast e c) = do
    e' <- absVarLoc' e
    return $ G2.Cast e' c
absVarLoc' (G2.Tick (G2.Breakpoint s) e) = do
    s' <- absLocSpan s
    let t' = G2.Breakpoint s'

    e' <- absVarLoc' e
    return $ G2.Tick t' e'
absVarLoc' (G2.Assume fc e1 e2) = do
    e1' <- absVarLoc' e1
    e2' <- absVarLoc' e2
    return $ G2.Assume fc e1' e2'
absVarLoc' (G2.Assert fc e1 e2) = do
    e1' <- absVarLoc' e1
    e2' <- absVarLoc' e2
    return $ G2.Assert fc e1' e2'
absVarLoc' e = return e

absLocSpan :: G2.Span -> IO G2.Span
absLocSpan s@G2.Span {G2.start = st, G2.end = en} = do
    st' <- absLoc st
    en' <- absLoc en
    return $ s {G2.start = st', G2.end = en'}

absLoc :: G2.Loc -> IO G2.Loc
absLoc l@G2.Loc {G2.file = f} = do
    f' <- makeAbsolute f
    return $ l {G2.file = f'}


-- When we don't want the 


-- Loading stuff
readFileExtractedG2 :: FilePath -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
readFileExtractedG2 file = do
  contents <- readFile file
  return $ read contents

readAllExtractedG2s :: FilePath -> FilePath -> IO [(G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)]
readAllExtractedG2s root file = go [file] HS.empty []
  where
    go :: [FilePath]
        -> HS.HashSet FilePath
        -> [(G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)]
        -> IO [(G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)]
    go [] _ accum = return accum
    go (tgt : todos) visited accum =
      let absPath = root ++ "/" ++ tgt in
      if HS.member absPath visited then
        go todos visited accum
      else do
        (nameMap, tyNameMap, exg2) <- readFileExtractedG2 absPath
        -- Dependencies are relative paths
        let deps = map (\d -> (T.unpack d) ++ ".g2i") $ G2.exg2_deps exg2

        let todos' = todos ++ deps
        let visited' = HS.insert absPath visited
        let accum' = accum ++ [(nameMap, tyNameMap, exg2)]
        go todos' visited' accum'


-- Merge nm2 into nm1
rewrireNameMap :: (T.Text, Maybe T.Text) -> G2.Name -> G2.NameMap -> G2.NameMap
rewrireNameMap key val@(G2.Name occ mod unq span) nameMap =
  case HM.lookup (occ, mod) nameMap of
    Nothing -> HM.insert key val nameMap
    Just new -> HM.insert key new nameMap

mergeNameMap :: G2.NameMap -> G2.NameMap -> G2.NameMap
mergeNameMap nm1 = foldr (\(key, name) nm1' -> rewrireNameMap key name nm1') nm1 . HM.toList


-- Favors earlier in the list
mergeFileExtractedG2s :: [(G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)]
    -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
mergeFileExtractedG2s [] = (HM.empty, HM.empty, G2.emptyExtractedG2)
mergeFileExtractedG2s (ex : []) = ex
mergeFileExtractedG2s ((nm1, tnm1, ex1) : (nm2, tnm2, ex2) : exs) =
  let nm' = mergeNameMap nm1 nm2 in
  let tnm' = mergeNameMap tnm1 tnm2 in
  let ex' = mergeExtractedG2s [ex1, ex2] in
    mergeFileExtractedG2s $ (nm', tnm', ex') : exs


