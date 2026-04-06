{-# LANGUAGE CPP, FlexibleContexts, LambdaCase, OverloadedStrings, TupleSections #-}

module G2.Plugin (plugin) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Plugins as GHC hiding ((<>))
#else
import GhcPlugins as GHC hiding ((<>))
#endif
import GHC.Unit.External
import GHC.Core.FamInstEnv
import GHC.Core.InstEnv
import GHC.Types.TyThing

import G2.Config
import G2.Initialization.MkCurrExpr
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import G2.Translation as T

import Control.Monad
import qualified Control.Monad.State.Lazy as SM
import Data.IORef
import System.IO.Unsafe
import System.Directory
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import Options.Applicative
import G2.Language.TyVarEnv as TV

-- | During symbolic execution, we need to know definitions, types, etc.
-- from previously compiled modules.  We also need to avoid reusing the same
-- names.  We use `compiledModules` to store both previously compiled modules
-- and existing Expression/Type Name maps.
compiledModules :: IORef (Maybe (ExtractedG2, NameMap, TypeNameMap))
compiledModules = unsafePerformIO $ newIORef Nothing
{-# NOINLINE compiledModules #-}

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

pluginConfig :: FilePath -> ParserInfo (String, Config)
pluginConfig homedir = 
    info ((,) <$> argument str (metavar "FUNCTION") <*> mkConfig homedir <**> helper)
          ( fullDesc
          <> progDesc "Symbolic Execution of Haskell code"
          <> header "The G2 Symbolic Execution Engine" )


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install cmd_lne todo = do
    env <- getHscEnv
    homedir <- liftIO $ getHomeDirectory
    (entry, config) <- liftIO . handleParseResult $ execParserPure defaultPrefs (pluginConfig homedir) cmd_lne
    return $ CoreDoPluginPass "G2" (g2PluginPass entry config env):todo

g2PluginPass :: String -> Config -> HscEnv -> ModGuts -> CoreM ModGuts
g2PluginPass entry config env modguts = do
    _ <- liftIO $ g2PluginPass' entry config env modguts
    return modguts

g2PluginPass' :: String -> Config -> HscEnv -> ModGuts -> IO ()
g2PluginPass' entry config env modguts = do
    -- We want simpl to be False so the simplifier does not run, because
    -- this plugin gets inserted into the simplifier.  Thus, running the simplifier
    -- results in an infinite loop.
    let tconfig = (simplTranslationConfig {simpl = False, load_rewrite_rules = True, hpc_ticks = False})
        ems = EnvModSumModGuts env [] [modguts]

    prev_comp <- readIORef compiledModules
    (base_exg2, base_nm, base_tnm) <- case prev_comp of
                                        Just prev -> return prev
                                        Nothing -> translateBase tconfig config [] Nothing

    (new_nm, new_tm, exg2) <- hskToG2ViaEMS tconfig ems base_nm base_tnm

    -- Get an initial set of relevant bindings to load from imports
    let rel_names = mconcat
                  . map (names . flip HM.lookup (exg2_binds exg2))
                  . filter (\(Name n _ _ _) -> n == T.pack entry)
                  $ HM.elems new_nm

    (imports_exg2, (imports_nm, import_tnm)) <- SM.runStateT (loadImports env rel_names) (new_nm, new_tm)

    let merged_exg2 = mergeExtractedG2s [exg2, imports_exg2, base_exg2]
        injected_exg2 = specialInject merged_exg2

        mod_names = exg2_mod_names exg2

    writeIORef compiledModules $ Just (merged_exg2, imports_nm, import_tnm)

    let simp_state = initSimpleState injected_exg2 imports_nm import_tnm


    let mod_name = moduleNameString . moduleName $ mg_module modguts

    case findFuncPlugin TV.empty (T.pack entry) [Just $ T.pack mod_name] (IT.expr_env simp_state) of
        Left (ie, _) -> do
            let (init_state, bindings) = initStateFromSimpleState simp_state mod_names False
                                        (mkCurrExpr TV.empty Nothing Nothing ie)
                                        (E.higherOrderExprs TV.empty . IT.expr_env)
                                        config

            _ <- runG2WithConfig [] [] ie "" [] mod_names init_state config bindings
            return ()

        Right _ -> return ()

-- Based on https://dl.acm.org/doi/pdf/10.1145/3495272
loadImports :: SM.MonadIO m => HscEnv -> Seq.Seq L.Name -> NamesT m ExtractedG2
loadImports env ns = do
    external_package_state <- liftIO $ hscEPS env
    let all_ids = nonDetNameEnvElts $ eps_PTE external_package_state
        all_tys = mapMaybe (\case
                                ATyCon t -> Just t
                                _ -> Nothing) all_ids
        all_binds = mapMaybe (\case
                                        AnId i -> fmap (i,) . maybeUnfoldingTemplate $ realIdUnfolding i
                                        _ -> Nothing) all_ids
    
    -- Compute bindings. The total number of binds is (very) large. As an optimization, we only convert binds
    -- that are actually relevant to the function(s) we are symbolically executing.
    rel_binds <- convertRelBinds ns HS.empty all_binds []
    binds <- mapM (uncurry (mkBindTuple Nothing)) rel_binds
    
    tycons <- mapM T.mkTyCon all_tys
    cls_insts <- mapM mkClass . instEnvElts $ eps_inst_env external_package_state
    fam_insts <- mapM mkFamilyAxioms . famInstEnvElts $ eps_fam_inst_env external_package_state
    let tycons' = mapMaybe (\(n, t) -> case t of Just t' -> Just (n, t'); Nothing -> Nothing) tycons
    return $ ExtractedG2 { exg2_mod_names = []
                         , exg2_binds = HM.fromList binds
                         , exg2_tycons = HM.fromList tycons'
                         , exg2_classes = cls_insts
                         , exg2_axioms = fam_insts
                         , exg2_exports = []
                         , exg2_deps = []
                         , exg2_rules = []}

-- | Compute bindings that are actually relevant to the passed list of "relevant names".
convertRelBinds :: SM.MonadIO m =>
                   Seq.Seq L.Name -- ^ Relevant names
                -> HS.HashSet L.Name -> [(GHC.Id, CoreExpr)] -> [(GHC.Id, CoreExpr)] -> NamesT m [(GHC.Id, CoreExpr)]
convertRelBinds Seq.Empty _ _ rel = return rel
convertRelBinds (n Seq.:<| ns) explored binds so_far_rel
    | n `notElem` explored = do
        rel_binds <- filterM (\(i, _) -> liftM2 (==) (valNameLookup $ varName i) (return n)) binds
        let n_rel_call = S.toList . mconcat $ map (relVar . snd) rel_binds
        n_rel_call_g2 <- mapM (valNameLookup . varName) n_rel_call
        let ns' = Seq.fromList n_rel_call_g2 <> ns
            explored' = HS.insert n explored
        convertRelBinds ns' explored' binds (rel_binds ++ so_far_rel)
    | otherwise = convertRelBinds ns explored binds so_far_rel

-- Compute the set of variables used in a (GHC Core) Expr
relVar :: GHC.Expr b -> S.Set GHC.Id
relVar (GHC.Var i) = S.singleton i
relVar (GHC.Lit _) = S.empty
relVar (GHC.App e1 e2) = relVar e1 <> relVar e2
relVar (GHC.Lam _ e) = relVar e
relVar (GHC.Let b e) =
    let
        relB (NonRec _ nr_e) = relVar nr_e
        relB (Rec nr_es) = mconcat $ map (relVar . snd) nr_es
    in
    relB b <> relVar e
relVar (GHC.Case e _ _ as) =
    relVar e <> mconcat (map (\(GHC.Alt _ _ a_e) -> relVar a_e) as)
relVar (GHC.Cast e _) = relVar e
relVar (GHC.Tick _ e) = relVar e
relVar (GHC.Type _) = S.empty
relVar (GHC.Coercion _) = S.empty

findFuncPlugin :: TV.TyVarEnv -> T.Text -> [Maybe T.Text] -> ExprEnv -> Either (L.Id, L.Expr) String
findFuncPlugin tv s m_mod eenv =
    case matchNames of
        [] -> Right $ "No functions with name " ++ (T.unpack s)
        pairs -> case filter (\(n, _) -> L.nameModule n `elem` m_mod) pairs of
                    [(n, e)] -> Left (Id n (typeOf tv e), e)
                    [] -> Right $ "No function with name " ++ (T.unpack s) ++ " in available modules"
                    _ -> Right $ "Multiple functions with same name " ++ (T.unpack s) ++
                                " in available modules"
    where
        matchNames =
            let
                splits = T.splitOn "." s
                spec_mod = T.intercalate "." (init splits)
                func = last splits
            in
            case spec_mod of
                "" -> E.toExprList $ E.filterWithKey (\n _ -> nameOcc n == s) eenv
                _ -> E.toExprList $ E.filterWithKey (\n _ -> nameOcc n == func && L.nameModule n == Just spec_mod) eenv
