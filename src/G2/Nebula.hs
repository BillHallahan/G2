module G2.Nebula (plugin) where

import GhcPlugins

import G2.Config
import G2.Equiv.Config
import G2.Equiv.Verifier
import qualified G2.Initialization.Types as IT
import G2.Interface
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import qualified G2.Solver as S
import G2.Translation

import Data.List
import qualified Data.Text as T
import Options.Applicative

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
    let tconfig = (TranslationConfig {simpl = False, load_rewrite_rules = True})
        ems = EnvModSumModGuts env [] [modguts]

    (base_exg2, b_nm, b_tnm) <- translateBase tconfig config [] Nothing

    (_, _, exg2) <- hskToG2ViaEMS tconfig ems b_nm b_tnm

    let merged_exg2 = mergeExtractedG2s [exg2, base_exg2]
        injected_exg2 = specialInject merged_exg2

    let simp_state = initSimpleState injected_exg2

        (init_state, bindings) = initStateFromSimpleState simp_state Nothing False
                                     (\_ ng _ _ _ _ _ -> (Prim Undefined TyBottom, [], [], ng))
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

checkRulePrinting :: Config
                  -> NebulaConfig
                  -> State t
                  -> Bindings
                  -> [T.Text] -- ^ names of forall'd variables required to be total
                  -> RewriteRule
                  -> IO (S.Result () () ())
checkRulePrinting config nebula_config init_state bindings total rule = do
    putStrLn $ "Checking " ++ (T.unpack $ L.ru_name rule)
    res <- checkRule config nebula_config init_state bindings total rule
    print res
    return res

