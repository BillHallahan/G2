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
import G2.Equiv.Config
import G2.Equiv.Verifier
import G2.Initialization.MkCurrExpr
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import qualified G2.Solver as S
import G2.Translation as T

import qualified Control.Monad.State.Lazy as SM
import Data.IORef
import System.IO.Unsafe
import System.Directory
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as T
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
    liftIO . putStrLn $ "base binds = " ++ show (length $ HM.keys $ exg2_binds base_exg2)

    (new_nm, new_tm, exg2) <- hskToG2ViaEMS tconfig ems base_nm base_tnm
    liftIO . putStrLn $ "new binds = " ++ show (length $ HM.keys $ exg2_binds exg2)

    (imports_exg2, (imports_nm, import_tnm)) <- SM.runStateT (loadImports env) (new_nm, new_tm)
    liftIO . putStrLn $ "import binds = " ++ show (nub $ map (\(Name _ m _ _) -> m) $ HM.keys $ exg2_binds imports_exg2)
    liftIO . putStrLn $ "import binds = " ++ show (length $ HM.keys $ exg2_binds imports_exg2)

    let merged_exg2 = mergeExtractedG2s [exg2, imports_exg2, base_exg2]
        injected_exg2 = specialInject merged_exg2

        mod_names = exg2_mod_names exg2

    writeIORef compiledModules $ Just (merged_exg2, imports_nm, import_tnm)

    let simp_state = initSimpleState injected_exg2 imports_nm import_tnm

    case findFunc TV.empty (T.pack entry) mod_names (IT.expr_env simp_state) of
        Left (ie, _) -> do
            let (init_state, bindings) = initStateFromSimpleState simp_state mod_names False
                                        (mkCurrExpr TV.empty Nothing Nothing ie)
                                        (E.higherOrderExprs TV.empty . IT.expr_env)
                                        config

            putStrLn $ "E.keys count " ++ show (length $ E.keys (IT.expr_env simp_state))
            T.putStrLn $ "About to run " <> nameOcc (L.idName ie)
            (er, b, to) <- runG2WithConfig [] [] ie "" [] mod_names init_state config bindings
            return ()

        Right errs -> return ()

-- Based on https://dl.acm.org/doi/pdf/10.1145/3495272
loadImports :: SM.MonadIO m => HscEnv -> NamesT m ExtractedG2
loadImports env = do
    external_package_state <- liftIO $ hscEPS env
    let package_iface = eps_PIT external_package_state
        all_mods = moduleEnvKeys package_iface
        
        all_ids = nonDetNameEnvElts $ eps_PTE external_package_state
        all_tys = mapMaybe (\case
                                ATyCon t -> Just t
                                _ -> Nothing) all_ids
        all_binds = mapMaybe (\case
                                        AnId i -> fmap (i,) . maybeUnfoldingTemplate $ realIdUnfolding i
                                        _ -> Nothing) all_ids
    liftIO . putStrLn $ "all mods = " ++ show (map (moduleNameString . moduleName) $ all_mods)
    liftIO . putStrLn $ "length all_binds = " ++ show (length all_binds)
    binds <- mapM (uncurry (mkBindTuple Nothing)) all_binds
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