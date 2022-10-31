{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Haskell Translation
module G2.Translation.Haskell
    ( loadProj
    , guessProj
    , hskToG2ViaModGuts
    , hskToG2ViaModGutsFromFile
    , hskToG2ViaCgGuts
    , hskToG2ViaCgGutsFromFile
    , mkCgGutsClosure
    , mkModDetailsClosure

    , EnvModSumModGuts
    , envModSumModGuts
    , hskToG2ViaEMS
    , envModSumModGutsImports

    , mergeExtractedG2s
    , mkExpr
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
    , findCabal
    ) where

import qualified G2.Language.TypeEnv as G2 (AlgDataTy (..))
import qualified G2.Language.Syntax as G2
-- import qualified G2.Language.Typing as G2
import qualified G2.Translation.TransTypes as G2

import G2.Translation.GHC

import Control.Monad

import qualified Data.Array as A
import qualified Data.ByteString.Char8 as C
import Data.Foldable
import Data.List
import Data.List.Split
import Data.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T
import Data.Tuple.Extra
import System.FilePath
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

loadProj ::  Maybe HscTarget -> [FilePath] -> [FilePath] -> [GeneralFlag] -> G2.TranslationConfig -> Ghc SuccessFlag
loadProj hsc proj src gflags tr_con = do
    beta_flags <- getSessionDynFlags
    let gen_flags = gflags

    let init_beta_flags = gopt_unset beta_flags Opt_StaticArgumentTransformation

    let beta_flags' = foldl' gopt_set init_beta_flags gen_flags
    let dflags = beta_flags' { -- Profiling fails to load a profiler friendly version of the base
                               -- without this special casing for hscTarget, but we can't use HscInterpreted when we have certain unboxed types
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
                               backend = if hostIsProfiled 
                                                then Interpreter
                                                else case hsc of
                                                    Just hsc' -> hsc'
                                                    _ -> backend beta_flags'
#else
                               hscTarget = if rtsIsProfiled 
                                                then HscInterpreted
                                                else case hsc of
                                                    Just hsc' -> hsc'
                                                    _ -> hscTarget beta_flags'
#endif
                             , ghcLink = LinkInMemory
                             , ghcMode = CompManager

                             , importPaths = proj ++ importPaths beta_flags'

                             , simplPhases = if G2.simpl tr_con then simplPhases beta_flags' else 0
                             , maxSimplIterations = if G2.simpl tr_con then maxSimplIterations beta_flags' else 0

                             , hpcDir = head proj}    
        dflags' = setIncludePaths proj dflags

    _ <- setSessionDynFlags dflags'
    targets <- mapM (flip guessTarget Nothing) src
    _ <- setTargets targets
    load LoadAllTargets

setIncludePaths :: [FilePath] -> DynFlags -> DynFlags
#if __GLASGOW_HASKELL__ < 806
setIncludePaths proj dflags = dflags { includePaths = proj ++ includePaths dflags }
#else
setIncludePaths proj dflags = dflags { includePaths = addQuoteInclude (includePaths dflags) proj }
#endif

-- Compilation pipeline with CgGuts
hskToG2ViaCgGutsFromFile :: Maybe HscTarget
  -> [FilePath]
  -> [FilePath]
  -> G2.NameMap
  -> G2.TypeNameMap
  -> G2.TranslationConfig
  -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaCgGutsFromFile hsc proj src nm tm tr_con = do
  ems <- envModSumModGuts hsc proj src tr_con
  hskToG2ViaEMS tr_con ems nm tm

hskToG2ViaEMS :: G2.TranslationConfig
              -> EnvModSumModGuts
              -> G2.NameMap
              -> G2.TypeNameMap
              -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaEMS tr_con ems nm tm = do
  closures <- mkCgGutsModDetailsClosuresFromEMS tr_con ems
  let (nm', tm', ex_g2) = hskToG2ViaCgGuts nm tm closures tr_con
  return (nm', tm', ex_g2)



hskToG2ViaCgGuts :: G2.NameMap
  -> G2.TypeNameMap
  -> [(G2.CgGutsClosure, G2.ModDetailsClosure)]
  -> G2.TranslationConfig
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaCgGuts nm tm pairs tr_con = do
  let (nm2, tm2, exg2s) = foldr (\(c, m) (nm', tm', exs) ->
                            let mgcc = cgGutsModDetailsClosureToModGutsClosure c m in
                            let (nm'', tm'', g2) = modGutsClosureToG2 nm' tm' mgcc tr_con in
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
    , G2.mgcc_rules = G2.cgcc_rules cg
    }


data EnvModSumModGuts = EnvModSumModGuts HscEnv [ModSummary] [ModGuts]

envModSumModGuts :: Maybe HscTarget
                 -> [FilePath]
                 -> [FilePath]
                 -> G2.TranslationConfig 
                 -> IO EnvModSumModGuts
envModSumModGuts hsc proj src tr_con =
  runGhc (Just libdir) $ do
      _ <- loadProj hsc proj src [] tr_con
      env <- getSession

      mod_graph <- getModuleGraph

      let msums = convertModuleGraph mod_graph
      parsed_mods <- mapM parseModule msums
      typed_mods <- mapM typecheckModule parsed_mods
      desug_mods <- mapM desugarModule typed_mods
      return . EnvModSumModGuts env msums $ map coreModule desug_mods

envModSumModGutsImports :: EnvModSumModGuts -> [String]
envModSumModGutsImports (EnvModSumModGuts _ ms _) = concatMap (map (\(_, L _ m) -> moduleNameString m) . ms_textual_imps) ms

mkCgGutsModDetailsClosuresFromEMS :: G2.TranslationConfig -> EnvModSumModGuts -> IO [( G2.CgGutsClosure, G2.ModDetailsClosure)]
#if __GLASGOW_HASKELL__ < 806
mkCgGutsModDetailsClosuresFromEMS tr_con (EnvModSumModGuts env _ modgutss) = do
  simplgutss <- mapM (if G2.simpl tr_con then hscSimplify env else return . id) modgutss
  tidys <- mapM (tidyProgram env) simplgutss
  let pairs = map (\((cg, md), mg) -> ( mkCgGutsClosure (mg_binds mg) cg
                                          , mkModDetailsClosure (mg_deps mg) md)) $ zip tidys simplgutss
  return pairs
#else
mkCgGutsModDetailsClosuresFromEMS tr_con (EnvModSumModGuts env _ modgutss) = do
  simplgutss <- mapM (if G2.simpl tr_con then hscSimplify env [] else return . id) modgutss
  tidys <- mapM (tidyProgram env) simplgutss
  let pairs = map (\((cg, md), mg) -> ( mkCgGutsClosure (mg_binds mg) cg
                                      , mkModDetailsClosure (mg_deps mg) md)) $ zip tidys simplgutss
  return pairs
#endif

-- | The core program in the CgGuts does not include local rules after tidying.
-- As such, we pass in the CoreProgram from the ModGuts
mkCgGutsClosure :: CoreProgram -> CgGuts -> G2.CgGutsClosure
mkCgGutsClosure bndrs cgguts =
  G2.CgGutsClosure
    { G2.cgcc_mod_name = Just $ moduleNameString $ moduleName $ cg_module cgguts
    , G2.cgcc_binds = cg_binds cgguts
    , G2.cgcc_breaks = cg_modBreaks cgguts
    , G2.cgcc_tycons = cg_tycons cgguts
    , G2.cgcc_rules = concatMap ruleInfoRules . map ruleInfo . map idInfo 
                            . concatMap bindersOf $ bndrs }


mkModDetailsClosure :: Dependencies -> ModDetails -> G2.ModDetailsClosure
mkModDetailsClosure deps moddet =
  G2.ModDetailsClosure
    { G2.mdcc_cls_insts = md_insts moddet
    , G2.mdcc_type_env = md_types moddet
    , G2.mdcc_exports = exportedNames moddet
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
    , G2.mdcc_deps = map (moduleNameString . gwib_mod) $ dep_mods deps
#else
    , G2.mdcc_deps = map (moduleNameString . fst) $ dep_mods deps
#endif
    }



-- Compilation pipeline with ModGuts
hskToG2ViaModGutsFromFile :: Maybe HscTarget
  -> [FilePath]
  -> [FilePath]
  -> G2.NameMap
  -> G2.TypeNameMap
  -> G2.TranslationConfig
  -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaModGutsFromFile hsc proj src nm tm tr_con = do
  closures <- mkModGutsClosuresFromFile hsc proj src tr_con
  return $ hskToG2ViaModGuts nm tm closures tr_con
   

hskToG2ViaModGuts :: G2.NameMap
  -> G2.TypeNameMap
  -> [G2.ModGutsClosure]
  -> G2.TranslationConfig
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaModGuts nm tm modgutss tr_con =
  let (nm2, tm2, exg2s) = foldr (\m (nm', tm', cls) ->
                                let (nm'', tm'', mc) = modGutsClosureToG2 nm' tm' m tr_con in
                                  (nm'', tm'', mc : cls))
                                (nm, tm, [])
                                modgutss in
    (nm2, tm2, mergeExtractedG2s exg2s)




modGutsClosureToG2 :: G2.NameMap
  -> G2.TypeNameMap
  -> G2.ModGutsClosure
  -> G2.TranslationConfig
  -> (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
modGutsClosureToG2 nm tm mgcc tr_con =
  let breaks = G2.mgcc_breaks mgcc in
  -- Do the binds
  let (nm2, binds) = foldr (\b (nm', bs) ->
                              let (nm'', bs') = mkBinds nm' tm breaks b in
                                (nm'', bs `HM.union` bs'))
                           (nm, HM.empty)
                           (G2.mgcc_binds mgcc) in
  -- Do the tycons
  let raw_tycons = G2.mgcc_tycons mgcc ++ typeEnvTyCons (G2.mgcc_type_env mgcc) in
  let (nm3, tm2, tycons) = foldr (\tc (nm', tm', tcs) ->
                                  let ((nm'', tm''), n, mb_t) = mkTyCon nm' tm' tc in
                                    (nm'', tm'', maybe tcs (\t -> HM.insert n t tcs) mb_t))
                                (nm2, tm, HM.empty)
                                raw_tycons in
  -- Do the class
  let classes = map (mkClass nm3 tm2) $ G2.mgcc_cls_insts mgcc in

  -- Do the rules
  let rules = if G2.load_rewrite_rules tr_con
                  then mapMaybe (mkRewriteRule nm3 tm2 breaks) $ G2.mgcc_rules mgcc
                  else [] in

  -- Do the exports
  let exports = G2.mgcc_exports mgcc in
  let deps = fmap T.pack $ G2.mgcc_deps mgcc in
    (nm3, tm2,
        G2.ExtractedG2
          { G2.exg2_mod_names = [fmap T.pack $ G2.mgcc_mod_name mgcc]
          , G2.exg2_binds = binds
          , G2.exg2_tycons = tycons
          , G2.exg2_classes = classes
          , G2.exg2_exports = exports
          , G2.exg2_deps = deps
          , G2.exg2_rules = rules })
  

mkModGutsClosuresFromFile :: Maybe HscTarget
  -> [FilePath]
  -> [FilePath]
  -> G2.TranslationConfig
  -> IO [G2.ModGutsClosure]
mkModGutsClosuresFromFile hsc proj src tr_con = do
  (env, modgutss) <- runGhc (Just libdir) $ do
      _ <- loadProj hsc proj src [] tr_con
      env <- getSession

      mod_graph <- getModuleGraph

      let msums = convertModuleGraph mod_graph
      parsed_mods <- mapM parseModule msums

      typed_mods <- mapM typecheckModule parsed_mods
      desug_mods <- mapM desugarModule typed_mods
      return (env, map coreModule desug_mods)

  if G2.simpl tr_con then do
    simpls <- mapM (hscSimplifyC env) modgutss
    mapM (mkModGutsClosure env) simpls
  else do
    mapM (mkModGutsClosure env) modgutss

{-# INLINE convertModuleGraph #-}
convertModuleGraph :: ModuleGraph -> [ModSummary]
#if __GLASGOW_HASKELL__ < 806
convertModuleGraph = id
#else
convertModuleGraph = mgModSummaries
#endif

{-# INLINE hscSimplifyC #-}
hscSimplifyC :: HscEnv -> ModGuts -> IO ModGuts
#if __GLASGOW_HASKELL__ < 806
hscSimplifyC = hscSimplify
#else
hscSimplifyC env = hscSimplify env []
#endif


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
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
      , G2.mgcc_deps = map (moduleNameString . gwib_mod) $ dep_mods $ mg_deps modguts
#else
      , G2.mgcc_deps = map (moduleNameString . fst) $ dep_mods $ mg_deps modguts
#endif
      , G2.mgcc_rules = mg_rules modguts
      }

-- Merging, order matters!
mergeExtractedG2s :: [G2.ExtractedG2] -> G2.ExtractedG2
mergeExtractedG2s [] = G2.emptyExtractedG2
mergeExtractedG2s (g2:g2s) =
  let g2' = mergeExtractedG2s g2s in
    G2.ExtractedG2
      { G2.exg2_mod_names = G2.exg2_mod_names g2 ++ G2.exg2_mod_names g2' -- order matters
      , G2.exg2_binds = G2.exg2_binds g2 `HM.union` G2.exg2_binds g2'
      , G2.exg2_tycons = G2.exg2_tycons g2 `HM.union` G2.exg2_tycons g2'
      , G2.exg2_classes = G2.exg2_classes g2 ++ G2.exg2_classes g2'
      , G2.exg2_exports = G2.exg2_exports g2 ++ G2.exg2_exports g2'
      , G2.exg2_deps = G2.exg2_deps g2 ++ G2.exg2_deps g2'
      , G2.exg2_rules = G2.exg2_rules g2 ++ G2.exg2_rules g2' }

----------------
-- Translating the individual components in CoreSyn, etc into G2 Core

mkBinds :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreBind -> (G2.NameMap, HM.HashMap G2.Name G2.Expr)
mkBinds nm tm mb (NonRec var expr) = 
    let
        (i, nm') = mkIdUpdatingNM var nm tm
    in
    (nm', HM.singleton (G2.idName i) (mkExpr nm' tm mb expr))
mkBinds nm tm mb (Rec ves) =
    second (HM.fromList) $
        mapAccumR (\nm' (v, e) ->
                    let
                        (i, nm'') = mkIdUpdatingNM v nm' tm
                    in
                    (nm'', (G2.idName i, mkExpr nm'' tm mb e))
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

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
createTickish :: Maybe ModBreaks -> GenTickish i -> Maybe G2.Tickish
#else
createTickish :: Maybe ModBreaks -> Tickish i -> Maybe G2.Tickish
#endif
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
mkId tm vid = G2.Id ((mkName . varName) vid) ((mkType tm . varType) vid)

-- Makes an Id, not respecting UniqueIds
mkIdUnsafe :: Id -> G2.Id
mkIdUnsafe vid = G2.Id ((mkName . varName) vid) (mkType HM.empty . varType $ vid)

mkIdLookup :: Id -> G2.NameMap -> G2.TypeNameMap -> G2.Id
mkIdLookup i nm tm =
    let
        n = mkNameLookup (varName i) nm
        t = mkType tm . varType $ i
    in
    G2.Id n t

mkIdUpdatingNM :: Id -> G2.NameMap -> G2.TypeNameMap -> (G2.Id, G2.NameMap)
mkIdUpdatingNM vid nm tm =
    let
        n@(G2.Name n' m _ _) = flip mkNameLookup nm . varName $ vid
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
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
mkSpan (RealSrcSpan s _) = Just $ mkRealSpan s
#else
mkSpan (RealSrcSpan s) = Just $ mkRealSpan s
#endif
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
#if __GLASGOW_HASKELL__ < 808
mkLit (MachChar chr) = G2.LitChar chr
mkLit (MachStr bstr) = G2.LitString (C.unpack bstr)
#else
mkLit (LitChar chr) = G2.LitChar chr
mkLit (LitString bstr) = G2.LitString (C.unpack bstr)
#endif

#if __GLASGOW_HASKELL__ < 806
mkLit (MachInt i) = G2.LitInt (fromInteger i)
mkLit (MachInt64 i) = G2.LitInt (fromInteger i)
mkLit (MachWord i) = G2.LitInt (fromInteger i)
mkLit (MachWord64 i) = G2.LitInt (fromInteger i)
mkLit (LitInteger i _) = G2.LitInteger (fromInteger i)
#elif __GLASGOW_HASKELL__ < 902
mkLit (LitNumber LitNumInteger i _) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumNatural i _) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumInt i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumInt64 i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord64 i _) = G2.LitInt (fromInteger i)
#else
mkLit (LitNumber LitNumInteger i) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumNatural i) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumInt i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumInt64 i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord64 i) = G2.LitInt (fromInteger i)
#endif

#if __GLASGOW_HASKELL__ < 808
mkLit (MachFloat rat) = G2.LitFloat rat
mkLit (MachDouble rat) = G2.LitDouble rat
#else
mkLit (LitFloat rat) = G2.LitFloat rat
mkLit (LitDouble rat) = G2.LitDouble rat
#endif
mkLit _ = error "mkLit: unhandled Lit"
-- mkLit (MachNullAddr) = error "mkLit: MachNullAddr"
-- mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreBind -> [(G2.Id, G2.Expr)]
mkBind nm tm mb (NonRec var expr) = [(mkId tm var, mkExpr nm tm mb expr)]
mkBind nm tm mb (Rec ves) = map (\(v, e) -> (mkId tm v, mkExpr nm tm mb e)) ves

mkAlts :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> [CoreAlt] -> [G2.Alt]
mkAlts nm tm mb = map (mkAlt nm tm mb)

mkAlt :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreAlt -> G2.Alt
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
mkAlt nm tm mb (Alt acon prms expr) = G2.Alt (mkAltMatch nm tm acon prms) (mkExpr nm tm mb expr)
#else
mkAlt nm tm mb (acon, prms, expr) = G2.Alt (mkAltMatch nm tm acon prms) (mkExpr nm tm mb expr)
#endif

mkAltMatch :: G2.NameMap -> G2.TypeNameMap -> AltCon -> [Var] -> G2.AltMatch
mkAltMatch nm tm (DataAlt dcon) params = G2.DataAlt (mkData nm tm dcon) (map (mkId tm) params)
mkAltMatch _ _ (LitAlt lit) _ = G2.LitAlt (mkLit lit)
mkAltMatch _ _ DEFAULT _ = G2.Default

mkType :: G2.TypeNameMap -> Type -> G2.Type
mkType tm (TyVarTy v) = G2.TyVar $ mkId tm v
mkType tm (AppTy t1 t2) = G2.TyApp (mkType tm t1) (mkType tm t2)
#if __GLASGOW_HASKELL__ < 808
mkType tm (FunTy t1 t2) = G2.TyFun (mkType tm t1) (mkType tm t2)
#elif __GLASGOW_HASKELL__ < 902
mkType tm (FunTy _ t1 t2) = G2.TyFun (mkType tm t1) (mkType tm t2)
#else
mkType tm (FunTy _ _ t1 t2) = G2.TyFun (mkType tm t1) (mkType tm t2)
#endif
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
    | G2.Name "Type" _ _ _ <- mkName $ tyConName tc = G2.TYPE
    | G2.Name "TYPE" _ _ _ <- mkName $ tyConName tc = G2.TYPE
    | otherwise = mkG2TyCon (mkTyConName tm tc) (map (mkType tm) ts) (mkType tm $ tyConKind tc) 

mkTyCon :: G2.NameMap -> G2.TypeNameMap -> TyCon -> ((G2.NameMap, G2.TypeNameMap), G2.Name, Maybe G2.AlgDataTy)
mkTyCon nm tm t = case dcs of
                        Just dcs' -> ((nm'', tm''), n, Just dcs')
                        Nothing -> ((nm'', tm''), n, Nothing)
  where
    n@(G2.Name n' m _ _) = flip mkNameLookup tm . tyConName $ t
    tm' = HM.insert (n', m) n tm

    nm' = foldr (uncurry HM.insert) nm
            $ map (\n_@(G2.Name n'_ m_ _ _) -> ((n'_, m_), n_)) 
            $ map (flip mkNameLookup nm . dataConName) $ visibleDataCons (algTyConRhs t)

    bv = map (mkId tm) $ tyConTyVars t

    (nm'', tm'', dcs) =
        case isAlgTyCon t of 
            True -> case algTyConRhs t of
                            DataTyCon { data_cons = dc } -> 
                                ( nm'
                                , tm'
                                , Just $ G2.DataTyCon bv $ map (mkData nm' tm) dc
                                )
                            NewTyCon { data_con = dc
                                     , nt_rhs = rhst} -> 
                                     ( nm'
                                     , tm'
                                     , Just $ G2.NewTyCon { G2.bound_ids = bv
                                                          , G2.data_con = mkData nm' tm dc
                                                          , G2.rep_type = mkType tm rhst}
                                     )
                            AbstractTyCon {} -> error "Unhandled TyCon AbstractTyCon"
                            -- TupleTyCon {} -> error "Unhandled TyCon TupleTyCon"
                            TupleTyCon { data_con = dc } ->
                              ( nm'
                              , tm'
                              , Just $ G2.DataTyCon bv $ [mkData nm' tm dc]
                              )
                            SumTyCon {} -> error "Unhandled TyCon SumTyCon"
            False -> case isTypeSynonymTyCon t of
                    True -> 
                        let
                            (tv, st) = fromJust $ synTyConDefn_maybe t
                            st' = mkType tm st
                            tv' = map (mkId tm) tv
                        in
                        (nm, tm', Just $ G2.TypeSynonym { G2.bound_ids = tv'
                                                        , G2.synonym_of = st'})
                    False -> (nm, tm, Nothing)
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
#if __GLASGOW_HASKELL__ < 808
mkTyBinder tm (TvBndr v _) = G2.NamedTyBndr (mkId tm v)
#else
mkTyBinder tm (Bndr v _) = G2.NamedTyBndr (mkId tm v)
#endif

mkCoercion :: G2.TypeNameMap -> Coercion -> G2.Coercion
mkCoercion tm c =
    let
        k = fmap (mkType tm) $ coercionKind c
    in
    (pFst k) G2.:~ (pSnd k)

mkClass :: G2.NameMap -> G2.TypeNameMap -> ClsInst -> (G2.Name, G2.Id, [G2.Id], [(G2.Type, G2.Id)])
mkClass nm tm (ClsInst { is_cls = c, is_dfun = dfun }) =
    ( flip mkNameLookup tm . className $ c
    , mkId tm dfun
    , map (mkId tm) $ classTyVars c
    , zip (map (mkType tm) $ classSCTheta c) (map (\i -> mkIdLookup i nm tm) $ classAllSelIds c) )


mkRewriteRule :: G2.NameMap -> G2.TypeNameMap -> Maybe ModBreaks -> CoreRule -> Maybe G2.RewriteRule
mkRewriteRule nm tm breaks (Rule { ru_name = n
                                 , ru_fn = fn
                                 , ru_rough = rough
                                 , ru_bndrs = bndrs
                                 , ru_args = args
                                 , ru_rhs = rhs }) =
    let
        r = G2.RewriteRule { G2.ru_name = T.pack $ unpackFS n
                           , G2.ru_head = mkNameLookup fn nm
                           , G2.ru_rough = map (fmap (flip mkNameLookup nm)) rough
                           , G2.ru_bndrs = map (mkId tm) bndrs
                           , G2.ru_args = map (mkExpr nm tm breaks) args
                           , G2.ru_rhs = mkExpr nm tm breaks rhs }
    in
    Just r
mkRewriteRule _ _ _ _ = Nothing

exportedNames :: ModDetails -> [G2.ExportedName]
exportedNames = concatMap availInfoNames . md_exports

availInfoNames :: AvailInfo -> [G2.ExportedName]
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
availInfoNames (Avail n) = [greNameToName n]
availInfoNames (AvailTC n ns) = mkName n:map greNameToName ns

greNameToName :: GreName -> G2.Name
greNameToName (NormalGreName n) = mkName n
greNameToName (FieldGreName fl) = mkName $ flSelector fl
#else
availInfoNames (Avail n) = [mkName n]
availInfoNames (AvailTC n ns _) = mkName n:map mkName ns
#endif

-- | absVarLoc'
-- Switches all file paths in Var namesand Ticks to be absolute
absVarLoc :: HM.HashMap G2.Name G2.Expr -> IO (HM.HashMap G2.Name G2.Expr)
absVarLoc = mapM absVarLoc'
        
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
rewriteNameMap :: (T.Text, Maybe T.Text) -> G2.Name -> G2.NameMap -> G2.NameMap
rewriteNameMap key val@(G2.Name occ md _ _) nameMap =
  case HM.lookup (occ, md) nameMap of
    Nothing -> HM.insert key val nameMap
    Just new -> HM.insert key new nameMap

mergeNameMap :: G2.NameMap -> G2.NameMap -> G2.NameMap
mergeNameMap nm1 = foldr (\(key, name) nm1' -> rewriteNameMap key name nm1') nm1 . HM.toList


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

-- Look for the directory that contains the first instance of a *.cabal file
guessProj :: FilePath -> IO FilePath
guessProj tgt = do
  absTgt <- makeAbsolute tgt
  let splits = splitOn "/" absTgt
  potentialDirs <- filterM (dirContainsCabal)
                    $ reverse -- since we prefer looking in backtrack manner
                    $ map (intercalate "/")
                    $ inits splits

  case potentialDirs of
    (d : _) -> return d
    -- Unable to find a .cabal file at all, so we take the first one
    -- with the file loped off.
    [] -> return $ takeDirectory absTgt

dirContainsCabal :: FilePath -> IO Bool
dirContainsCabal "" = return False
dirContainsCabal dir = do
  exists <- doesDirectoryExist dir
  if exists then do
    files <- listDirectory dir   
    return $ any (\f -> ".cabal" `isSuffixOf` f) files
  else
    return $ False

findCabal :: FilePath -> IO (Maybe FilePath)
findCabal fp = do
  dir <- guessProj fp
  files <- listDirectory dir
  return $ find (\f -> ".cabal" `isSuffixOf` f) files