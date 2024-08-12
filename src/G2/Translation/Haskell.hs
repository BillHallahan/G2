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
    , mkModGutsClosure

    , EnvModSumModGuts (..)
    , envModSumModGutsFromFile
    , hskToG2ViaEMS
    , envModSumModGutsImports

    , mergeExtractedG2s
    , mkExpr
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
    
    , mkIdUnsafe
    , mkTyConNameUnsafe
    , mkDataUnsafe
    ) where

import qualified G2.Language.TypeEnv as G2 (AlgDataTy (..))
import qualified G2.Language.Syntax as G2
-- import qualified G2.Language.Typing as G2
import qualified G2.Translation.TransTypes as G2

import G2.Translation.GHC

import Control.Monad
import qualified Control.Monad.State.Lazy as SM

import qualified Data.Array as A
import qualified Data.ByteString.Char8 as C
import Data.Foldable
import Data.List
import Data.List.Split
import Data.Maybe
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T
import System.FilePath
import System.Directory
import G2.Language.AlgDataTy (ADTSource(..))

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
            [ ("GHC.BaseMonad", "GHC.Base")
            , ("GHC.Classes2", "GHC.Classes")
            , ("GHC.Types2", "GHC.Types")
            , ("GHC.Integer2", "GHC.Integer")
#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
            , ("GHC.Integer.Type2", "GHC.Num.Integer")
#else
            , ("GHC.Integer.Type2", "GHC.Integer.Type")
#endif
            , ("GHC.PrimSMT", "GHC.Prim")
            , ("GHC.Prim2", "GHC.Prim")
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
            , ("GHC.Tuple2", "GHC.Tuple.Prim")
#else
            , ("GHC.Tuple2", "GHC.Tuple")
#endif
            , ("GHC.Magic2", "GHC.Magic")
            , ("GHC.CString2", "GHC.CString")
            , ("Data.Map.Base", "Data.Map")]

loadProj :: Maybe HscTarget -> [FilePath] -> [FilePath] -> [GeneralFlag] -> G2.TranslationConfig -> Ghc SuccessFlag
loadProj hsc proj src gflags tr_con = do
    beta_flags <- getSessionDynFlags
    let gen_flags = if G2.hpc_ticks tr_con then Opt_Hpc:gflags else gflags

    let init_beta_flags = gopt_unset beta_flags Opt_StaticArgumentTransformation

    let beta_flags' = foldl' gopt_set init_beta_flags gen_flags
    let dflags = beta_flags' {
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
                               backend = case hsc of
                                            Just hsc' -> hsc'
                                            _ -> backend beta_flags'
#elif MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
                               backend = if hostIsProfiled 
                                                then Interpreter
                                                else case hsc of
                                                    Just hsc' -> hsc'
                                                    _ -> backend beta_flags'
#elif MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
                               hscTarget = if hostIsProfiled 
                                                then HscInterpreted
                                                else case hsc of
                                                    Just hsc' -> hsc'
                                                    _ -> hscTarget beta_flags'

#else
                               hscTarget = if rtsIsProfiled 
                                                then HscInterpreted
                                                else case hsc of
                                                    Just hsc' -> hsc'
                                                    _ -> hscTarget beta_flags'
#endif
#if MIN_VERSION_GLASGOW_HASKELL(9,4,0,0)
                             -- Profiling gives warnings without this special case
                             , targetWays_ = if hostIsProfiled then addWay WayProf (targetWays_ beta_flags') else targetWays_ beta_flags'
#endif
                             , ghcLink = LinkInMemory
                             , ghcMode = CompManager

                             , importPaths = proj ++ importPaths beta_flags'

                             , simplPhases = if G2.simpl tr_con then simplPhases beta_flags' else 0
                             , maxSimplIterations = if G2.simpl tr_con then maxSimplIterations beta_flags' else 0

                             , hpcDir = head proj}    
        dflags' = setIncludePaths proj dflags

    _ <- setSessionDynFlags dflags'
#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
    targets <- mapM (\s -> guessTarget s Nothing Nothing) src
#else
    targets <- mapM (flip guessTarget Nothing) src
#endif
    _ <- setTargets targets
    load LoadAllTargets

setIncludePaths :: [FilePath] -> DynFlags -> DynFlags
setIncludePaths proj dflags = dflags { includePaths = addQuoteInclude (includePaths dflags) proj }

-- Compilation pipeline with CgGuts
hskToG2ViaCgGutsFromFile :: Maybe HscTarget
  -> [FilePath]
  -> [FilePath]
  -> G2.NameMap
  -> G2.TypeNameMap
  -> G2.TranslationConfig
  -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaCgGutsFromFile hsc proj src nm tm tr_con = do
  ems <- envModSumModGutsFromFile hsc proj src tr_con
  hskToG2ViaEMS tr_con ems nm tm

hskToG2ViaEMS :: G2.TranslationConfig
              -> EnvModSumModGuts
              -> G2.NameMap
              -> G2.TypeNameMap
              -> IO (G2.NameMap, G2.TypeNameMap, G2.ExtractedG2)
hskToG2ViaEMS tr_con (EnvModSumModGuts env _ modgutss) nm tm = do
  closures <- mkCgGutsModDetailsClosures tr_con env modgutss
  let (ex_g2, (nm', tm')) = SM.runState (hskToG2ViaCgGuts closures tr_con) (nm, tm)
  return (nm', tm', ex_g2)

hskToG2ViaCgGuts :: [(G2.CgGutsClosure, G2.ModDetailsClosure)]
                 -> G2.TranslationConfig
                 -> G2.NamesM G2.ExtractedG2
hskToG2ViaCgGuts pairs tr_con = do
    exg2s <- mapM (\(c, m) -> do
                            let mgcc = cgGutsModDetailsClosureToModGutsClosure c m
                            g2 <- modGutsClosureToG2 mgcc tr_con
                            return g2)
                            pairs
    return $ mergeExtractedG2s exg2s


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

envModSumModGutsFromFile :: Maybe HscTarget
                         -> [FilePath]
                         -> [FilePath]
                         -> G2.TranslationConfig
                         -> IO EnvModSumModGuts
envModSumModGutsFromFile hsc proj src tr_con =
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

-- | Extract information from GHC into a form that G2 can process.
mkCgGutsModDetailsClosures :: G2.TranslationConfig -> HscEnv -> [ModGuts] -> IO [( G2.CgGutsClosure, G2.ModDetailsClosure)]
mkCgGutsModDetailsClosures tr_con env modgutss = do
  simplgutss <- mapM (if G2.simpl tr_con then hscSimplify env [] else return . id) modgutss

#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
  tidy_opts <- initTidyOpts env
  tidys <- mapM (tidyProgram tidy_opts) simplgutss
#else
  tidys <- mapM (tidyProgram env) simplgutss
#endif

  let pairs = map (\((cg, md), mg) -> ( mkCgGutsClosure (mg_binds mg) cg md
                                      , mkModDetailsClosure (mg_deps mg) md)) $ zip tidys simplgutss
  return pairs

-- | Extract information from GHC into a form that G2 can process.
mkCgGutsClosure :: CoreProgram -> CgGuts -> ModDetails -> G2.CgGutsClosure
mkCgGutsClosure binds cgguts md =
  let
      binds_rules = concatMap ruleInfoRules
                  . map ruleInfo
                  . map idInfo 
                  . concatMap bindersOf $ binds
  in
  G2.CgGutsClosure
    { G2.cgcc_mod_name = Just $ moduleNameString $ moduleName $ cg_module cgguts
    , G2.cgcc_binds = cg_binds cgguts
    , G2.cgcc_breaks = cg_modBreaks cgguts
    , G2.cgcc_tycons = cg_tycons cgguts
    -- Getting all rules is complicated by GHC's build process.  GHC goes through a "tidying"
    -- process, which performs various transformation on the Core code. Unfortunately:
    --    1) The core program in the CgGuts does not include rules after tidying.
    --    2) The ModDetails does not include all rules after tidying.
    --    3) Names of functions in rules in the original CoreProgram may have been changed by bindings
    --       (in which case it seems like those rules ARE in the ModDetails.)
    -- We can't just take the rules from the ModDetails, because some are eliminated during tidying.
    -- But we can't just take the rules from the original CoreProgram, because they might have function/variables
    -- names that no longer exist.
    -- As such, we keep:
    --    1) Rules from the ModDetails
    --    2) Rules from the CoreProgram, IF a rule with the same name is not in ModDetails
    , G2.cgcc_rules = nubBy (\r1 r2 -> ru_name r1 == ru_name r2) (md_rules md ++ binds_rules) }


mkModDetailsClosure :: Dependencies -> ModDetails -> G2.ModDetailsClosure
mkModDetailsClosure deps moddet =
  G2.ModDetailsClosure
    { G2.mdcc_cls_insts = getClsInst moddet
    , G2.mdcc_type_env = md_types moddet
    , G2.mdcc_exports = exportedNames moddet
    , G2.mdcc_deps = getModuleNames deps
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
  let (ex_g2, (nm', tm')) = SM.runState (hskToG2ViaModGuts closures tr_con) (nm, tm)
  return (nm', tm', ex_g2)
   

hskToG2ViaModGuts :: [G2.ModGutsClosure]
                  -> G2.TranslationConfig
                  -> G2.NamesM G2.ExtractedG2
hskToG2ViaModGuts modgutss tr_con = do
    exg2s <- mapM (\m -> modGutsClosureToG2 m tr_con) modgutss
    return $ mergeExtractedG2s exg2s

modGutsClosureToG2 :: G2.ModGutsClosure
                   -> G2.TranslationConfig
                   -> G2.NamesM G2.ExtractedG2
modGutsClosureToG2 mgcc tr_con = do
  let breaks = G2.mgcc_breaks mgcc
  -- Do the binds
  binds <- foldM (\bs b -> do
                          bs' <- mkBinds breaks b
                          return $ bs `HM.union` bs')
                 HM.empty
                 (G2.mgcc_binds mgcc)
  -- Do the tycons
  let raw_tycons = G2.mgcc_tycons mgcc ++ typeEnvTyCons (G2.mgcc_type_env mgcc)
  tycons <- foldM (\tcs tc -> do
                        (n, mb_t) <- mkTyCon tc
                        return $ maybe tcs (\t -> HM.insert n t tcs) mb_t)
                      HM.empty
                      raw_tycons
  -- Do the class
  classes <- mapM mkClass $ G2.mgcc_cls_insts mgcc

  -- Do the rules
  rules <- if G2.load_rewrite_rules tr_con
                  then mapM (mkRewriteRule breaks) $ G2.mgcc_rules mgcc
                  else return []

  -- Do the exports
  let exports = G2.mgcc_exports mgcc
  let deps = fmap T.pack $ G2.mgcc_deps mgcc
  return (G2.ExtractedG2
            { G2.exg2_mod_names = [fmap T.pack $ G2.mgcc_mod_name mgcc]
            , G2.exg2_binds = binds
            , G2.exg2_tycons = tycons
            , G2.exg2_classes = classes
            , G2.exg2_exports = exports
            , G2.exg2_deps = deps
            , G2.exg2_rules = catMaybes rules })
  

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
convertModuleGraph = mgModSummaries

{-# INLINE hscSimplifyC #-}
hscSimplifyC :: HscEnv -> ModGuts -> IO ModGuts
hscSimplifyC env = hscSimplify env []

-- This one will need to do the Tidy program stuff
mkModGutsClosure :: HscEnv -> ModGuts -> IO G2.ModGutsClosure
mkModGutsClosure env modguts = do
#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
  tidy_opts <- initTidyOpts env
  (cgguts, moddets) <- tidyProgram tidy_opts modguts
#else
  (cgguts, moddets) <- tidyProgram env modguts
#endif
  return
    G2.ModGutsClosure
      { G2.mgcc_mod_name = Just $ moduleNameString $ moduleName $ cg_module cgguts
      , G2.mgcc_binds = cg_binds cgguts
      , G2.mgcc_tycons = cg_tycons cgguts
      , G2.mgcc_breaks = cg_modBreaks cgguts
      , G2.mgcc_cls_insts = getClsInst moddets
      , G2.mgcc_type_env = md_types moddets
      , G2.mgcc_exports = exportedNames moddets
      , G2.mgcc_deps = getModuleNames $ mg_deps modguts
      , G2.mgcc_rules = mg_rules modguts
      }

getClsInst :: ModDetails -> [ClsInst]
#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
getClsInst = instEnvElts . md_insts
#else
getClsInst = md_insts
#endif

getModuleNames :: Dependencies -> [String]
#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
getModuleNames = map moduleNameString . dep_sig_mods
#elif MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
getModuleNames = map (moduleNameString . gwib_mod) . dep_mods
#else
getModuleNames = map (moduleNameString . fst) . dep_mods
#endif

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

mkBinds :: Maybe ModBreaks -> CoreBind -> G2.NamesM (HM.HashMap G2.Name G2.Expr)
mkBinds mb (NonRec var expr) = do
    i <- mkIdLookup var
    e <- mkExpr mb expr
    return $ HM.singleton (G2.idName i) e
mkBinds mb (Rec ves) =
    return . HM.fromList =<<
        mapM (\(v, expr) -> do
                  i <- mkIdLookup v
                  e <- mkExpr mb expr
                  return (G2.idName i, e)) ves

mkExpr :: Maybe ModBreaks -> CoreExpr -> G2.NamesM G2.Expr
mkExpr _ (Var var) = return . G2.Var =<< mkIdLookup var
mkExpr _ (Lit lit) = return $ G2.Lit (mkLit lit)
mkExpr mb (App fxpr axpr) = liftM2 G2.App (mkExpr mb fxpr) (mkExpr mb axpr)
mkExpr mb (Lam var expr) = liftM2 (G2.Lam (mkLamUse var)) (valId var) (mkExpr mb expr)
mkExpr mb (Let bnd expr) = liftM2 G2.Let (mkBind mb bnd) (mkExpr mb expr)
mkExpr mb (Case mxpr var t alts) = do
    bindee <- mkExpr mb mxpr
    binder <- valId var
    ty <- mkType t
    as <- mkAlts mb alts
    return $ G2.Case bindee binder ty as
mkExpr mb (Cast expr c) =  liftM2 G2.Cast (mkExpr mb expr) (mkCoercion c)
mkExpr _ (Coercion c) = liftM G2.Coercion (mkCoercion c)
mkExpr mb (Tick t expr) =
    case createTickish mb t of
        Just t' -> return . G2.Tick t' =<< mkExpr mb expr
        Nothing -> mkExpr mb expr
mkExpr _ (Type ty) = liftM G2.Type (mkType ty)

#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
createTickish :: Maybe ModBreaks -> GenTickish i -> Maybe G2.Tickish
#else
createTickish :: Maybe ModBreaks -> Tickish i -> Maybe G2.Tickish
#endif
createTickish (Just mb) (Breakpoint {breakpointId = bid}) =
    case mkSpan $ modBreaks_locs mb A.! bid of
        Just s -> Just $ G2.Breakpoint $ s
        Nothing -> Nothing
createTickish _ (HpcTick { tickModule = md, tickId = i}) =
    Just . G2.HpcTick i . T.pack . moduleNameString $ moduleName md
createTickish _ _ = Nothing

mkLamUse :: Id -> G2.LamUse
mkLamUse v
    | isTyVar v = G2.TypeL
    | otherwise = G2.TermL

valId :: Id -> G2.NamesM G2.Id
valId vid = liftM2 G2.Id (valNameLookup . varName $ vid) (mkType . varType $ vid)

typeId :: Id -> G2.NamesM G2.Id
typeId vid = liftM2 G2.Id (typeNameLookup . varName $ vid) (mkType . varType $ vid)

mkIdLookup :: Id -> G2.NamesM G2.Id
mkIdLookup i = do
    n <- valNameLookup (varName i)
    t <- mkType . varType $ i
    return $ G2.Id n t

mkName :: Name -> G2.Name
mkName name = G2.Name occ mdl unq sp
  where
    occ = T.pack . occNameString . nameOccName $ name
    unq = (getKey . nameUnique) name
    mdl = case nameModule_maybe name of
              Nothing -> Nothing
              Just md -> switchModule (T.pack . moduleNameString . moduleName $ md)

    sp = mkSpan $ getSrcSpan name

valNameLookup :: Name -> G2.NamesM G2.Name
valNameLookup n = do
    (nm, tm) <- SM.get
    (n', nm') <- nameLookup nm n
    SM.put (nm', tm)
    return n'

typeNameLookup :: Name -> G2.NamesM G2.Name
typeNameLookup n = do
    (nm, tm) <- SM.get
    (n', tm') <- nameLookup tm n
    SM.put (nm, tm')
    return n'

nameLookup :: HM.HashMap (T.Text, Maybe T.Text) G2.Name -> Name -> G2.NamesM (G2.Name, HM.HashMap (T.Text, Maybe T.Text) G2.Name)
nameLookup nm name = do
    -- We only lookup in the G2.NameMap if the Module name is not Nothing
    -- Internally, a module may use multiple variables with the same name and a module Nothing
    return $ case mdl of
                  Nothing -> (G2.Name occ mdl unq sp, nm)
                  _ -> case HM.lookup (occ, mdl) nm of
                          Just (G2.Name n' m i _) -> (G2.Name n' m i sp, nm)
                          Nothing -> let n = G2.Name occ mdl unq sp in (n, HM.insert (occ, mdl) n nm)
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

#if __GLASGOW_HASKELL__ <= 810
mkLit (LitNumber LitNumInteger i _) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumNatural i _) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumInt i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumInt64 i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord i _) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord64 i _) = G2.LitInt (fromInteger i)
#elif __GLASGOW_HASKELL__ <= 902
mkLit (LitNumber LitNumInteger i) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumNatural i) = G2.LitInteger (fromInteger i)
mkLit (LitNumber LitNumInt i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumInt64 i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord64 i) = G2.LitInt (fromInteger i)
#else
mkLit (LitNumber LitNumInt i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumInt64 i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord i) = G2.LitInt (fromInteger i)
mkLit (LitNumber LitNumWord64 i) = G2.LitInt (fromInteger i)
#endif

#if __GLASGOW_HASKELL__ < 808
mkLit (MachFloat rat) = G2.LitFloat (fromRational rat)
mkLit (MachDouble rat) = G2.LitDouble (fromRational rat)
#else
mkLit (LitFloat rat) = G2.LitFloat (fromRational rat)
mkLit (LitDouble rat) = G2.LitDouble (fromRational rat)
#endif
mkLit _ = error "mkLit: unhandled Lit"
-- mkLit (MachNullAddr) = error "mkLit: MachNullAddr"
-- mkLit (MachLabel _ _ _ ) = error "mkLit: MachLabel"

mkBind :: Maybe ModBreaks -> CoreBind -> G2.NamesM [(G2.Id, G2.Expr)]
mkBind mb (NonRec var expr) = do
    i <- valId var
    e <- mkExpr mb expr
    return [(i, e)]
mkBind mb (Rec ves) = mapM (\(v, e) -> do i <- valId v
                                          e' <- mkExpr mb e
                                          return (i, e')) ves

mkAlts :: Maybe ModBreaks -> [CoreAlt] -> G2.NamesM [G2.Alt]
mkAlts mb = mapM (mkAlt mb)

mkAlt :: Maybe ModBreaks -> CoreAlt -> G2.NamesM G2.Alt
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
mkAlt mb (Alt acon prms expr) = liftM2 G2.Alt (mkAltMatch acon prms) (mkExpr mb expr)
#else
mkAlt mb (acon, prms, expr) = liftM2 G2.Alt (mkAltMatch acon prms) (mkExpr mb expr)
#endif

mkAltMatch :: AltCon -> [Var] -> G2.NamesM G2.AltMatch
mkAltMatch (DataAlt dcon) params = liftM2 G2.DataAlt (mkData dcon) (mapM valId params)
mkAltMatch (LitAlt lit) _ = return $ G2.LitAlt (mkLit lit)
mkAltMatch DEFAULT _ = return G2.Default

mkType :: Type -> G2.NamesM G2.Type
mkType (TyVarTy v) = liftM G2.TyVar $ typeId v
mkType (AppTy t1 t2) = liftM2 G2.TyApp (mkType t1) (mkType t2)
#if __GLASGOW_HASKELL__ < 808
mkType (FunTy t1 t2) = liftM2 G2.TyFun (mkType t1) (mkType t2)
#elif __GLASGOW_HASKELL__ <= 810
mkType (FunTy _ t1 t2) = liftM2 G2.TyFun (mkType t1) (mkType t2)
#else
mkType (FunTy _ _ t1 t2) = liftM2 G2.TyFun (mkType t1) (mkType t2)
#endif
mkType (ForAllTy b ty) = liftM2 G2.TyForAll (mkTyBinder b) (mkType ty)
mkType (LitTy _) = return G2.TyBottom
-- mkType (CastTy _ _) = error "mkType: CastTy"
mkType (CastTy _ _) = return G2.TyUnknown
mkType (CoercionTy _) = return G2.TyUnknown
-- mkType (CoercionTy _) = error "mkType: Coercion"
mkType (TyConApp tc ts)
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
#else
    | isFunTyCon tc
    , length ts == 2 =
        case ts of
            [t1, t2] -> liftM2 G2.TyFun (mkType t1) (mkType t2)
            _ -> error "mkType: non-arity 2 FunTyCon from GHC"
#endif
    | G2.Name "Type" _ _ _ <- mkName $ tyConName tc = return G2.TYPE
    | G2.Name "TYPE" _ _ _ <- mkName $ tyConName tc = return G2.TYPE
    | G2.Name "->" _ _ _ <- mkName $ tyConName tc
    , [_, _, t1, t2] <- ts = liftM2 G2.TyFun (mkType t1) (mkType t2)
    | otherwise = liftM3 mkG2TyCon (mkTyConName tc) (mapM mkType ts) (mkType $ tyConKind tc) 

mkTyCon :: TyCon -> G2.NamesM (G2.Name, Maybe G2.AlgDataTy)
mkTyCon t = do
    n@(G2.Name n' m _ _) <- typeNameLookup . tyConName $ t

    (nm, tm) <- SM.get
    let tm' = HM.insert (n', m) n tm
  
    dc_names <- mapM (valNameLookup . dataConName) $ visibleDataCons (algTyConRhs t)
    let nm' = foldr (uncurry HM.insert) nm
            . map (\n_@(G2.Name n'_ m_ _ _) -> ((n'_, m_), n_)) 
            $ dc_names 

    bv <- mapM typeId $ tyConTyVars t

    dcs <-
        case isAlgTyCon t of
            True -> do
                      SM.put (nm', tm')
                      case algTyConRhs t of
                            DataTyCon { data_cons = dc} -> do
                                dcs <- mapM mkData dc
                                return . Just $ G2.DataTyCon bv dcs ADTSourceCode
                            NewTyCon { data_con = dc
                                     , nt_rhs = rhst} -> do
                                        dc' <- mkData dc
                                        t' <- mkType rhst
                                        return .
                                          Just $ G2.NewTyCon { G2.bound_ids = bv
                                                             , G2.data_con = dc'
                                                             , G2.rep_type = t'
                                                             , G2.adt_source = ADTSourceCode}
                            AbstractTyCon {} -> error "Unhandled TyCon AbstractTyCon"
                            -- TupleTyCon {} -> error "Unhandled TyCon TupleTyCon"
                            TupleTyCon { data_con = dc } -> do
                              dc' <- mkData dc
                              return . Just $ G2.DataTyCon bv [dc'] ADTSourceCode
                            SumTyCon {} -> error "Unhandled TyCon SumTyCon"
            False -> case isTypeSynonymTyCon t of
                    True -> do
                        SM.put (nm, tm')
                        let (tv, st) = fromJust $ synTyConDefn_maybe t
                        st' <- mkType st
                        tv' <- mapM typeId tv
                        return . Just $ G2.TypeSynonym { G2.bound_ids = tv'
                                                       , G2.synonym_of = st'
                                                       , G2.adt_source = ADTSourceCode}
                    False -> return Nothing

    case dcs of
        Just dcs' -> return (n, Just dcs')
        Nothing -> return (n, Nothing)

mkTyConName :: TyCon -> G2.NamesM G2.Name
mkTyConName tc = typeNameLookup (tyConName tc)

mkData :: DataCon -> G2.NamesM G2.DataCon
mkData datacon = do
    name <- mkDataName datacon
    ty <- (mkType . dataConRepType) datacon
    return $ G2.DataCon name ty

mkDataName :: DataCon -> G2.NamesM G2.Name
mkDataName datacon = valNameLookup . dataConName $ datacon

mkTyBinder :: TyVarBinder -> G2.NamesM G2.Id
#if __GLASGOW_HASKELL__ < 808
mkTyBinder (TvBndr v _) = typeId v
#else
mkTyBinder (Bndr v _) = typeId v
#endif

mkCoercion :: Coercion -> G2.NamesM G2.Coercion
mkCoercion c = do
    let (Pair t1 t2) = coercionKind c
    t1' <- mkType t1
    t2' <- mkType t2
    return $ t1' G2.:~ t2'

mkClass :: ClsInst -> G2.NamesM (G2.Name, G2.Id, [G2.Id], [(G2.Type, G2.Id)])
mkClass (ClsInst { is_cls = c, is_dfun = dfun }) = do
    class_name <-  typeNameLookup . className $ c
    i <- valId dfun
    tyvars <- mapM typeId $ classTyVars c

    sctheta <- mapM mkType $ classSCTheta c
    sel_ids <- mapM mkIdLookup $ classAllSelIds c
    let sctheta_selids = zip sctheta sel_ids
    return ( class_name
           , i
           , tyvars
           , sctheta_selids)


mkRewriteRule :: Maybe ModBreaks -> CoreRule -> G2.NamesM (Maybe G2.RewriteRule)
mkRewriteRule breaks (Rule { ru_name = n
                           , ru_origin = mdl
                           , ru_fn = fn
                           , ru_rough = rough
                           , ru_bndrs = bndrs
                           , ru_args = args
                           , ru_rhs = rhs }) = do
    head_name <- valNameLookup fn
    rough' <- mapM (maybe (return Nothing) (\nm -> return . Just =<< valNameLookup nm)) rough
    bndrs' <- mapM valId bndrs
    args' <- mapM (mkExpr breaks) args
    rhs' <- mkExpr breaks rhs
    let r = G2.RewriteRule { G2.ru_name = T.pack $ unpackFS n
                           , G2.ru_module = T.pack . moduleNameString $ moduleName mdl
                           , G2.ru_head = head_name
                           , G2.ru_rough = rough'
                           , G2.ru_bndrs = bndrs'
                           , G2.ru_args = args'
                           , G2.ru_rhs = rhs' }
    return $ Just r
mkRewriteRule _ _ = return Nothing

exportedNames :: ModDetails -> [G2.ExportedName]
exportedNames = concatMap availInfoNames . md_exports

availInfoNames :: AvailInfo -> [G2.ExportedName]
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
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
absVarLoc' (G2.Case e i t as) = do
    e' <- absVarLoc' e
    as' <- mapM (\(G2.Alt a ae) -> return . G2.Alt a =<< absVarLoc' ae) as
    return $ G2.Case e' i t as'
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
guessProj :: Maybe [FilePath] -> FilePath -> IO [FilePath]
guessProj (Just fp) _ = return fp
guessProj Nothing tgt = do
  absTgt <- makeAbsolute tgt
  let splits = splitOn "/" absTgt
  potentialDirs <- filterM (dirContainsCabal)
                    $ reverse -- since we prefer looking in backtrack manner
                    $ map (intercalate "/")
                    $ inits splits

  case potentialDirs of
    (d : _) -> return [d]
    -- Unable to find a .cabal file at all, so we take the first one
    -- with the file loped off.
    [] -> return $ [takeDirectory absTgt]

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
  dir <- guessProj Nothing fp
  files <- mapM listDirectory dir
  return $ find (\f -> ".cabal" `isSuffixOf` f) (concat files)

-------------------------------------------------------------------------------
-- Unsafe construction
-------------------------------------------------------------------------------

mkUnsafe :: G2.NamesM a -> a
mkUnsafe nms = SM.evalState nms (HM.empty, HM.empty)

-- | Makes an Id, not respecting uniques
mkIdUnsafe :: Id -> G2.Id
mkIdUnsafe vid = 
    mkUnsafe (liftM2 G2.Id (return . mkName . varName $ vid) (mkType . varType $ vid))

-- | Makes a TyCon, not respecting uniques
mkTyConNameUnsafe :: TyCon -> G2.Name
mkTyConNameUnsafe tc = mkUnsafe (mkTyConName tc)

-- | Makes a Data, not respecting uniques
mkDataUnsafe :: DataCon -> G2.DataCon
mkDataUnsafe dc = mkUnsafe (mkData dc)
