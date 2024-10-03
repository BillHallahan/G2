{-# LANGUAGE CPP, FlexibleContexts #-}

module G2.Nebula (plugin) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Plugins
#else
import GhcPlugins
#endif

import G2.Config
import G2.Equiv.Config
import G2.Equiv.Verifier
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import qualified G2.Solver as S
import G2.Translation

import Data.IORef
import System.IO.Unsafe
import Data.List
import qualified Data.Text as T
import Options.Applicative

-- | During symbolic execution, we need to know definitions, types, etc.
-- from previously compiled modules.  We also need to avoid reusing the same
-- names.  We use `compiledModules` to store both previously compiled modules
-- and existing Expression/Type Name maps.
compiledModules :: IORef (Maybe (ExtractedG2, NameMap, TypeNameMap))
compiledModules = unsafePerformIO $ newIORef Nothing
{-# NOINLINE compiledModules #-}

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install cmd_lne todo = do
    env <- getHscEnv
    let pr_nebula_config = getNebulaConfigPlugin cmd_lne
    (entry, nebula_config) <- liftIO $ handleParseResult pr_nebula_config
    return $ CoreDoPluginPass "Nebula" (nebulaPluginPass entry nebula_config env):todo

nebulaPluginPass :: Maybe String -> NebulaConfig -> HscEnv -> ModGuts -> CoreM ModGuts
nebulaPluginPass m_entry nebula_config env modguts = do
    _ <- liftIO $ nebulaPluginPass' m_entry nebula_config env modguts
    return modguts

nebulaPluginPass' :: Maybe String -> NebulaConfig -> HscEnv -> ModGuts -> IO ()
nebulaPluginPass' m_entry nebula_config env modguts = do
    config <- getConfigDirect
    -- We want simpl to be False so the simplifier does not run, because
    -- this plugin get's inserted into the simplifier.  Thus, running the implifier
    -- results in an infinite loop.
    let tconfig = (simplTranslationConfig {simpl = False, load_rewrite_rules = True, hpc_ticks = False})
        ems = EnvModSumModGuts env [] [modguts]

    prev_comp <- readIORef compiledModules
    (prev_exg2, prev_nm, prev_tnm) <- case prev_comp of
                                        Just prev -> return prev
                                        Nothing -> translateBase tconfig config [] Nothing

    (new_nm, new_tm, exg2) <- hskToG2ViaEMS tconfig ems prev_nm prev_tnm

    let merged_exg2 = mergeExtractedG2s [exg2, prev_exg2]
        injected_exg2 = specialInject merged_exg2
    writeIORef compiledModules $ Just (merged_exg2, new_nm, new_tm)

    let simp_state = initSimpleState injected_exg2

        (init_state, bindings) = initStateFromSimpleState simp_state Nothing False
                                     (\_ ng _ _ _ _ -> (Prim Undefined TyBottom, [], [], Nothing, ng))
                                     (E.higherOrderExprs . IT.expr_env)
                                     config
    
    let total = []
    case m_entry of
        Just entry -> do
            let tentry = T.pack entry
            let rule = find (\r -> tentry == L.ru_name r) (rewrite_rules bindings)
                rule' = case rule of
                          Just r -> r
                          Nothing -> error "not found"
            _ <- checkRulePrinting config nebula_config init_state bindings total rule'
            return ()
        Nothing -> do
            let mod_name = T.pack . moduleNameString . moduleName . mg_module $ modguts
            mapM_ (checkRulePrinting config nebula_config init_state bindings total)
                $ filter (\r -> L.ru_module r == mod_name) (rewrite_rules bindings)

checkRulePrinting :: (ASTContainer t L.Type, ASTContainer t L.Expr) => Config
                  -> NebulaConfig
                  -> State t
                  -> Bindings
                  -> [T.Text] -- ^ names of forall'd variables required to be total
                  -> RewriteRule
                  -> IO (S.Result () () ())
checkRulePrinting config nebula_config init_state bindings total rule = do
    let rule_name = T.unpack $ L.ru_name rule
        nebula_config' = case log_rule nebula_config of
                              Just n -> if n == rule_name then nebula_config
                                        else nebula_config {log_states = NoLog}
                              Nothing -> nebula_config
    putStrLn $ "Log-rule nebula config = " ++ show (log_rule nebula_config)
    putStrLn $ "Checking " ++ rule_name
    res <- checkRule config nebula_config' init_state bindings total rule 
    case res of
        S.SAT _ -> putStrLn $ rule_name ++ " - counterexample found"
        S.UNSAT _ -> putStrLn $ rule_name ++ " - verified"
        S.Unknown _ _ -> putStrLn $ rule_name ++ " - unknown result"
    return res

