{-# LANGUAGE BangPatterns, CPP, DeriveDataTypeable, DeriveGeneric, 
             FlexibleContexts, LambdaCase, OverloadedStrings, TupleSections #-}

module G2.Plugin (SymEx (..), plugin) where

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
import G2.Interface
import G2.Initialization.Types as IT
import G2.Language as L
import qualified G2.Language.ExprEnv as E
import G2.Translation as T

import Control.Monad
import qualified Control.Monad.State.Strict as SM
import Data.Data
import qualified Data.Foldable as F
import GHC.Generics (Generic)
import Control.DeepSeq
import Data.IORef
import System.IO.Unsafe
import System.Directory
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Sequence as Seq
import qualified Data.Text.IO as T
import Options.Applicative
import G2.Language.TyVarEnv as TV

data SymEx = SymEx
           | SymExWithConfig String
             deriving (Data, Generic)

instance NFData SymEx

-- | During symbolic execution, we need to know definitions, types, etc.
-- from previously compiled modules.  We also need to avoid reusing the same
-- names.  We use `compiledModules` to store both previously compiled modules
-- and existing Expression/Type Name maps.
compiledModules :: IORef (Maybe (ExtractedG2, NameMap, TypeNameMap))
compiledModules = unsafePerformIO $ newIORef Nothing
{-# NOINLINE compiledModules #-}

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

pluginConfig :: FilePath -> ParserInfo Config
pluginConfig homedir = 
    info (mkConfig homedir <**> helper)
          ( fullDesc
          <> progDesc "Symbolic Execution of Haskell code"
          <> header "The G2 Symbolic Execution Engine" )


install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install cmd_lne todo = do
    env <- getHscEnv
    homedir <- liftIO $ getHomeDirectory
    config <- liftIO . handleParseResult $ execParserPure defaultPrefs (pluginConfig homedir) cmd_lne
    return $ CoreDoPluginPass "G2" (g2PluginPass cmd_lne config env):todo

g2PluginPass :: [CommandLineOption] -> Config -> HscEnv -> ModGuts -> CoreM ModGuts
g2PluginPass cmd_lne config env modguts = do
    _ <- g2PluginPass' cmd_lne config env modguts
    return modguts

g2PluginPass' :: [CommandLineOption] -> Config -> HscEnv -> ModGuts -> CoreM ()
g2PluginPass' cmd_lne config env modguts = do
    -- We want simpl to be False so the simplifier does not run, because
    -- this plugin gets inserted into the simplifier.  Thus, running the simplifier
    -- results in an infinite loop.
    let tconfig = (simplTranslationConfig {simpl = False, load_rewrite_rules = True, hpc_ticks = False})
        ems = EnvModSumModGuts env [] [modguts]

    prev_comp <- liftIO $ readIORef compiledModules
    (base_exg2, base_nm, base_tnm) <- case prev_comp of
                                        Just prev -> return prev
                                        Nothing -> liftIO $ translateBase tconfig config [] Nothing

    (new_nm, new_tm, exg2) <- liftIO $ hskToG2ViaEMS tconfig ems base_nm base_tnm

    -- Get the names of functions we are going to be symbolically executing
    let binders (NonRec b _) = [b]
        binders (Rec b) = map fst b
    all_fs <- mapM (\b -> (,b) <$> (annotationsOn modguts b :: CoreM [SymEx])) (concatMap binders $ mg_binds modguts)
    let fs = filter (not . null . fst) all_fs
    let ann_fs_g2 = SM.evalState (mapM (\(ann, b) -> do
                                        n <- valNameLookup . varName $ b
                                        return (ann, n)) fs) (new_nm, new_tm)
        fs_g2 = map snd ann_fs_g2

    -- Get an initial set of relevant bindings to load from imports
    let rel_names = deepseq ann_fs_g2
                  . Seq.fromList
                  . filter (`elem` fs_g2)
                  $ HM.elems new_nm

    let merged_new_base = mergeExtractedG2s [exg2, base_exg2]

    (imports_exg2, (imports_nm, import_tnm)) <- SM.runStateT (loadImports env (exg2_binds merged_new_base) rel_names) (new_nm, new_tm)

    let merged_exg2 = mergeExtractedG2s [merged_new_base, imports_exg2]
        injected_exg2 = specialInject merged_exg2

    liftIO $ writeIORef compiledModules $ Just (merged_exg2, imports_nm, import_tnm)

    let simp_state = initSimpleState injected_exg2 imports_nm import_tnm


    liftIO $ mapM_ (uncurry (runFunc cmd_lne simp_state)) ann_fs_g2

runFunc :: [CommandLineOption] -> SimpleState -> [SymEx] -> L.Name -> IO ()
runFunc cmd_lne simp_state symex_annot entry
    | Just (entry_name, e) <- E.lookupNameMod (L.nameOcc entry) (L.nameModule entry) (IT.expr_env simp_state) = do
        -- Get a Config to run this specific function
        homedir <- liftIO $ getHomeDirectory
        let func_cmd_line = case symex_annot of
                                [SymExWithConfig extra_cmd_lne] -> cmd_lne ++ words extra_cmd_lne
                                _ -> cmd_lne
        func_config <- liftIO . handleParseResult $ execParserPure defaultPrefs (pluginConfig homedir) func_cmd_line

        -- Run symbolic execution
        let entry_id = Id entry_name $ L.typeOf TV.empty e
        T.putStrLn $ "Running " <> nameOcc entry
        let (init_state, bindings) = initStateFromSimpleState simp_state [L.nameModule entry] False
                                    (mkCurrExpr TV.empty Nothing Nothing entry_id)
                                    (E.higherOrderExprs TV.empty . IT.expr_env)
                                    func_config
            bindings' = bindings { higher_order_inst = HS.empty }

        _ <- liftIO $ runG2WithConfig [] [] entry_id "" [] [L.nameModule entry] init_state func_config bindings'
        return ()
    | otherwise = return ()

-- Based on https://dl.acm.org/doi/pdf/10.1145/3495272
loadImports :: SM.MonadIO m => HscEnv -> HM.HashMap L.Name L.Expr -> Seq.Seq L.Name -> NamesT m ExtractedG2
loadImports env local_binds ns = do
    external_package_state <- liftIO $ hscEPS env
    let all_ids = nonDetNameEnvElts $ eps_PTE external_package_state
        all_tys = mapMaybe (\case
                                ATyCon t -> Just t
                                _ -> Nothing) all_ids
        all_imp_binds = mapMaybe (\case
                                        AnId i -> fmap (i,) . maybeUnfoldingTemplate $ realIdUnfolding i
                                        _ -> Nothing) all_ids
    
    -- Compute bindings. The total number of binds is (very) large. As an optimization, we only convert binds
    -- that are actually relevant to the function(s) we are symbolically executing.
    rel_binds <- convertRelBinds local_binds all_imp_binds (S.fromList $ F.toList ns) S.empty []
    liftIO $ putStrLn $ "length rel_binds = " ++ show (length rel_binds)
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
                    HM.HashMap L.Name L.Expr
                -> [(GHC.Id, CoreExpr)]
                -> S.Set L.Name -- ^ Relevant names
                -> S.Set L.Name
                -> [(GHC.Id, CoreExpr)]
                -> NamesT m [(GHC.Id, CoreExpr)]
convertRelBinds local_binds binds = go
    where
        go to_explore _ rel | S.null to_explore = return rel
        go to_explore explored so_far_rel
            | n `notElem` explored = do
                -- Find relevent bindings from the imports
                rel_binds <- filterM (\(i, _) -> liftM2 (==) (valNameLookup $ varName i) (return n)) binds
                let n_rel_call = S.toList . mconcat $ map (relVar . snd) rel_binds
                n_rel_call_g2 <- mapM (valNameLookup . varName) n_rel_call

                -- Find relevant local bindings to search deeper for needed imports
                let local_names = maybe S.empty topVarNames $ HM.lookup n local_binds
                liftIO . putStrLn $ "n = " ++ show n ++  "     local = " ++ show (length local_names) ++ "     ns = " ++ show (length ns)

                let ns' = ((S.fromList n_rel_call_g2 <> local_names) `S.difference` explored) <> ns
                    explored' = S.insert n explored
                go ns' explored' (rel_binds ++ so_far_rel)
            | otherwise = go ns explored so_far_rel
            where
                Just (n, ns) = S.minView to_explore

topVarNames :: L.Expr -> S.Set L.Name
topVarNames = go HS.empty
    where
        go bound (L.Var (Id n _)) | n `notElem` bound = S.singleton n
        go bound (L.Lam _ (Id b _) e) = go (HS.insert b bound) e
        go bound (L.Let kvs e) =
            let
                bound' = foldr HS.insert bound (map (L.idName . fst) kvs) 
            in
            S.unions $ map (go bound') (e:map snd kvs)
        go bound (L.Case e cvar _ as) =
            let
                bound' = HS.insert (L.idName cvar) bound

                add (L.DataAlt _ is) = foldr (HS.insert) bound' (map L.idName is)
                add (L.LitAlt _) = bound'
                add L.Default = bound'
            in
            S.unions $ go bound' e:map (\(L.Alt am ae) -> go (add am) ae) as
        go bound e = evalChildren (go bound) e

-- Compute the set of variables used in a (GHC Core) Expr
relVar :: GHC.CoreExpr -> S.Set GHC.Id
relVar = go S.empty
    where
        go bound (GHC.Var i) | i `notElem` bound = S.singleton i
                            | otherwise = S.empty
        go _ (GHC.Lit _) = S.empty
        go bound (GHC.App e1 e2) = go bound e1 <> go bound e2
        go bound (GHC.Lam i e) = go (S.insert i bound) e
        go bound (GHC.Let b e) =
            let
                newIds (NonRec i _) = S.singleton i
                newIds (Rec nr_es) = S.fromList $ map fst nr_es

                bound' = bound `S.union` newIds b

                relB (NonRec _ nr_e) = go bound' nr_e
                relB (Rec nr_es) = mconcat $ map (go bound' . snd) nr_es
            in
            relB b <> go bound' e
        go bound (GHC.Case e i _ as) =
            let
                bound' = S.insert i bound
            in
            go bound' e <> mconcat (map (\(GHC.Alt _ is a_e) -> go (foldr S.insert bound' is) a_e) as)
        go bound (GHC.Cast e _) = go bound e
        go bound (GHC.Tick _ e) = go bound e
        go _ (GHC.Type _) = S.empty
        go _ (GHC.Coercion _) = S.empty

annotationsOn :: Data a => ModGuts -> CoreBndr -> CoreM [a]
annotationsOn guts bndr = do
  (_, anns) <- getAnnotations deserializeWithData guts
  return $ lookupWithDefaultUFM anns [] (varName bndr)
