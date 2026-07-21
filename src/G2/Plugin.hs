{-# LANGUAGE BangPatterns, CPP, DeriveDataTypeable, DeriveGeneric,
             FlexibleContexts, LambdaCase, MagicHash, OverloadedStrings, ScopedTypeVariables, TupleSections #-}

module G2.Plugin (SymEx (..)
                 , plugin
                 , logAcceptedStateTime
                 
                 , assume
                 , G2.Plugin.assert
                 , (==>)

                 , smtLen
                 , (+++)
                 , smtAppend

                 , comp
                ) where

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import GHC.Plugins as GHC hiding ((<>))
#else
import GhcPlugins as GHC hiding ((<>))
#endif
import GHC.Unit.External
import GHC.Core.FamInstEnv
import GHC.Core.InstEnv
import GHC.Exts
import GHC.Types.TyThing

import G2.Config
import G2.Data.Utils (firstJust)
import G2.Execution.FuncConstraints
import G2.Initialization.MkCurrExpr
import G2.Interface
import G2.Initialization.Types as IT
import G2.Language as L
import G2.Language.KnownValues as KV
import qualified G2.Language.ExprEnv as E
import G2.Plugin.Prim
import G2.Translation as T

import qualified Control.Exception as Ex
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
import qualified Data.Text as TX

import System.Clock

data SymEx = SymEx
           | SymExWithConfig String
           | SMTEquivIs String -- ^ A corresponding SMT definition function name, which should be checked for equivalence
           | SMTEquivIsWithConfig String String -- ^ A corresponding SMT definition function name, which should be checked for equivalence
             deriving (Show, Data, Generic)

instance NFData SymEx

-- | Assume that a condition is true
assume :: Bool -- ^ Condition to assume
       -> a -- ^ 
       -> a
assume _ x = x

{-# NOINLINE assert #-}
-- | Assert that a condition is true
assert :: Bool -- ^ Condition to assert
       -> a -- ^ 
       -> a
assert _ x = x

-- | Implies
(==>) :: Bool -> Bool -> Bool
(==>) = assume
infixr 0 ==>

-- | During symbolic execution, we need to know definitions, types, etc.
-- from previously compiled modules.  We also need to avoid reusing the same
-- names.  We use `compiledModules` to store both previously compiled modules
-- and existing Expression/Type Name maps.
compiledModules :: IORef (Maybe (ExtractedG2, NameMap, TypeNameMap, S.Set L.Name))
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
    (new_nm, new_tm, ex_g2, prev_explored) <- loadExtractedG2 config env modguts

    -- Get the names of functions we are going to be symbolically executing
    ann_fs_g2 <- getBinderAnnotations new_nm new_tm modguts
    let fs_g2 = map fst ann_fs_g2

    -- Get an initial set of relevant bindings to load from imports
    let rel_names = Seq.fromList
                  . filter (`elem` fs_g2)
                  $ HM.elems new_nm
        -- comp is a function defined in this module used for checking equivalence,
        -- we add it to rel_names here to make sure it is loaded
        (comp_name, comp_nm) = addName "comp" (Just "G2.Plugin") new_nm

    (imports_nm, import_tnm, injected_exg2) <- setUpImports comp_nm new_tm env ex_g2 prev_explored (comp_name Seq.:<| rel_names)
    let simp_state = initSimpleState injected_exg2 imports_nm import_tnm

    let equivTo (Name _ eq_m _ _) (SMTEquivIs eq_n) | Just (smt_n, smt_e) <- (E.lookupNameMod (TX.pack eq_n) eq_m $ IT.expr_env simp_state) =
            Just (L.Var (Id smt_n $ L.typeOf TV.empty smt_e))
        equivTo _ _ = Nothing
        equiv_annots = HM.fromList $ mapMaybe (\(n, anns) -> (n,) <$> firstJust (equivTo n) anns) ann_fs_g2

    liftIO $ mapM_ (uncurry (runSymexAnnots cmd_lne equiv_annots simp_state)) ann_fs_g2

addName :: TX.Text -> Maybe TX.Text -> NameMap -> (L.Name, NameMap)
addName occ md nm | Just n <- HM.lookup (occ, md) nm = (n, nm)
                  | otherwise = (Name occ md 0 Nothing, HM.insert (occ, md) (Name occ md 0 Nothing) nm)

------------------------------------------------------------------------------
-- Run Symbolic Execution
------------------------------------------------------------------------------

runSymexAnnots :: [CommandLineOption]
               -> HM.HashMap L.Name L.Expr -- Real definitions to SMT definitions
               -> SimpleState
               -> L.Name
               -> [SymEx]
               -> IO ()
runSymexAnnots cmd_lne equiv_annots simp_state entry = mapM_ (runSymexAnnot cmd_lne equiv_annots simp_state entry)

runSymexAnnot :: [CommandLineOption] -> HM.HashMap L.Name L.Expr -> SimpleState -> L.Name -> SymEx -> IO ()
runSymexAnnot cmd_lne _ simp_state entry SymEx =
    runFunc cmd_lne simp_state entry
runSymexAnnot cmd_lne _ simp_state entry (SymExWithConfig extra_cmd_lne) =
    runFunc (cmd_lne ++ words extra_cmd_lne) simp_state entry
runSymexAnnot cmd_lne equiv_annots simp_state entry (SMTEquivIs smt_equiv_f) =
    checkEquiv cmd_lne equiv_annots simp_state entry smt_equiv_f
runSymexAnnot cmd_lne equiv_annots simp_state entry (SMTEquivIsWithConfig smt_equiv_f extra_cmd_lne) =
    checkEquiv (cmd_lne ++ words extra_cmd_lne) equiv_annots simp_state entry smt_equiv_f

runFunc :: [CommandLineOption] -> SimpleState -> L.Name -> IO ()
runFunc cmd_lne simp_state entry
    | Just (entry_name, e) <- E.lookupNameMod (L.nameOcc entry) (L.nameModule entry) (IT.expr_env simp_state) = do
        -- Get a Config to run this specific function
        homedir <- liftIO $ getHomeDirectory
        func_config <- liftIO . handleParseResult $ execParserPure defaultPrefs (pluginConfig homedir) cmd_lne

        -- Run symbolic execution
        let entry_id = Id entry_name $ L.typeOf TV.empty e
            entry_name' = case higherOrderSolver func_config of
                            SymConstraints -> nameOcc entry <> "_sym_constraints"
                            SymbolicFunc -> nameOcc entry <> "_symbolic"
                            _ -> nameOcc entry
        T.putStrLn $ "Running " <> entry_name'
        logAcceptedStateTime (TX.unpack entry_name')
        let (init_state, bindings) = initStateFromSimpleState simp_state [L.nameModule entry] False
                                    (mkCurrExpr TV.empty Nothing Nothing entry_id)
                                    (E.higherOrderExprs TV.empty . IT.expr_env)
                                    func_config
            bindings' = bindings { higher_order_inst = HS.empty }

        (_, _, _, time_outs, TimeInFC timeInFC) <- liftIO $ runG2WithConfig [] [] entry_id "" [] [L.nameModule entry] init_state func_config bindings'
        let seconds_in_fc = fromInteger (toNanoSecs timeInFC) / (10 ^ (9 :: Int) :: Double)
        -- Clean it up later, move this in some sort of Util
        let fc_file = "time_logs/fc_time.txt"
        file_exists <- doesFileExist fc_file
        when file_exists $ appendFile fc_file $ "\n" ++ TX.unpack entry_name' ++ " : " ++ show seconds_in_fc
        reportTerminationResults time_outs func_config
        return ()
    | otherwise = return ()

logAcceptedStateTime :: [Char] -> IO ()
logAcceptedStateTime entryName  = do
    let file_name = "time_logs/state_accept_log.txt"
    file_exists <- doesFileExist file_name
    when file_exists $ appendFile file_name $ "\n" ++ entryName ++ " : "

checkEquiv :: [CommandLineOption] -> HM.HashMap L.Name L.Expr -> SimpleState -> L.Name -> String -> IO ()
checkEquiv cmd_lne equiv_annots simp_state entry_real entry_smt
    | Just (entry_real_name, real_e) <- E.lookupNameMod (L.nameOcc entry_real) (L.nameModule entry_real) (IT.expr_env simp_state)
    , Just (entry_smt_name, _) <- E.lookupNameMod (TX.pack entry_smt) (L.nameModule entry_real) (IT.expr_env simp_state)
    , Just (comp_name, comp_e) <- E.lookupNameMod "comp" (Just "G2.Plugin") (IT.expr_env simp_state) = do
        -- Get a Config to run this specific function
        homedir <- liftIO $ getHomeDirectory
        func_config <- liftIO . handleParseResult $ execParserPure defaultPrefs (pluginConfig homedir) cmd_lne
        let func_config' = func_config { step_limit = False
                                       , smt_strings = UseSMTStrings
                                       , smt_prim_lists = UseSMTSeq { add_to_dcs = True, add_to_funcs = True }
                                       , smt_strings_strictness = StrictSMTStrings
                                       , search_strat = Subpath
                                       , min_found = 1 }

        let entry_id = Id entry_real_name $ L.typeOf TV.empty real_e
            (init_state, bindings) = initStateFromSimpleState simp_state [L.nameModule entry_real] False
                                (mkCurrExpr TV.empty Nothing Nothing entry_id)
                                (E.higherOrderExprs TV.empty . IT.expr_env)
                                func_config'
            bindings' = bindings { higher_order_inst = HS.empty }

            eenv = L.expr_env init_state
            kv = L.known_values init_state
            tv_env = tyvar_env init_state

            real_var = L.Var (L.Id entry_real_name $ L.typeOf tv_env real_e)
            smt_var = L.Var (L.Id entry_smt_name $ L.typeOf tv_env real_e)

            -- Modify the real function to replace recursive calls with calls to the SMT definitions
            real_e_mod_def = case E.lookup entry_real_name eenv of
                                    Just e -> e
                                    Nothing -> error "checkEquiv: definition not found"
            real_e' = replaceVars equiv_annots real_e_mod_def
            eenv' = E.insert entry_real_name real_e' eenv
        
            -- Set up a call to compare the real and SMT definitions
            in_vars = mapMaybe (flip E.lookup eenv) $ input_names bindings'
            call_real = mkApp (real_var:in_vars)
            call_smt = mkApp (smt_var:in_vars)
            eq = fromMaybe (error "checkEquiv: could not generate Eq typeclass")
               $ typeClassInst (L.type_classes init_state) HM.empty (KV.eqTC kv) (L.typeOf tv_env call_real)

            comp_expr = mkApp [ L.Var (L.Id comp_name $ L.typeOf tv_env comp_e)
                              , L.Type TyUnknown
                              , eq
                              , call_real
                              , call_smt]
            comp_state = init_state { L.expr_env = eenv'
                                    , curr_expr = CurrExpr Evaluate comp_expr
                                    , true_assert = False }
        (ers, _, _, time_outs, _) <- liftIO $ runG2WithConfig
                                                            [] [] entry_id "" []
                                                            [L.nameModule entry_real_name]
                                                            comp_state
                                                            func_config'
                                                            bindings'
        case ers of
            [] | NoTimeOut <- time_outs -> putStrLn $ "Equivalent: "
                                    <> TX.unpack (nameOcc entry_real_name) <> " and "
                                    <> TX.unpack (nameOcc entry_smt_name)
            _ | TimedOut _ <- time_outs -> putStrLn $ "Time Out: "
                                                <> TX.unpack (nameOcc entry_real_name) <> " and "
                                                <> TX.unpack (nameOcc entry_smt_name)
            _ -> putStrLn $ "Inequivalent: "
                                    <> TX.unpack (nameOcc entry_real_name) <> " and "
                                    <> TX.unpack (nameOcc entry_smt_name)

        return ()
    | otherwise = do
        putStrLn "checkEquiv: functions not found"
        return ()

replaceVars :: HM.HashMap L.Name L.Expr -> L.Expr -> L.Expr
replaceVars m = modify go
    where
        go (L.Var (Id n _)) | Just e <- HM.lookup n m = e
        go e = e

------------------------------------------------------------------------------
-- Loading in functions and function annotations
------------------------------------------------------------------------------

-- | Set up an initial extracted G2 with the base library and the functions from the module currently being compiled.
loadExtractedG2 :: Config -> HscEnv -> ModGuts -> CoreM (NameMap, TypeNameMap, ExtractedG2, S.Set L.Name)
loadExtractedG2 config env modguts = do
    -- We want simpl to be False so the simplifier does not run, because
    -- this plugin gets inserted into the simplifier.  Thus, running the simplifier
    -- results in an infinite loop.
    let tconfig = (simplTranslationConfig { simpl = False
                                          , load_rewrite_rules = True
                                          , hpc_ticks = True })
        ems = EnvModSumModGuts env [] [modguts]

    prev_comp <- liftIO $ readIORef compiledModules
    (base_exg2, base_nm, base_tnm, prev_explored) <- case prev_comp of
                                        Just prev -> return prev
                                        Nothing -> do
                                            (b_exg2, b_nm, b_tnm) <- liftIO $ translateBase tconfig config [] Nothing
                                            let expl = S.fromList . map fst . HM.toList $ exg2_binds b_exg2
                                            return (b_exg2, b_nm, b_tnm, expl)

    (new_nm, new_tm, exg2) <- liftIO $ hskToG2ViaEMS tconfig ems base_nm base_tnm
    let merged_exg2 = mergeExtractedG2s [exg2, base_exg2]
        injected_exg2 = specialInject merged_exg2
    return (new_nm, new_tm, injected_exg2, prev_explored)

getBinderAnnotations :: forall ann . (Data ann, NFData ann) => NameMap -> TypeNameMap -> ModGuts -> CoreM [(L.Name, [ann])]
getBinderAnnotations nm tm modguts = do
    let binders (NonRec b _) = [b]
        binders (Rec b) = map fst b
    all_fs <- mapM (\b -> (,b) <$> (annotationsOn modguts b :: CoreM [ann])) (concatMap binders $ mg_binds modguts)
    let fs = filter (not . null . fst) all_fs
    let anns = SM.evalState (mapM (\(ann, b) -> do
                                    n <- valNameLookup . varName $ b
                                    return (n, ann)) fs) (nm, tm)
    return $ deepseq anns anns

-- | Add relevant functions from the imports into the ExtractedG2.
setUpImports :: SM.MonadIO m => NameMap -> TypeNameMap -> HscEnv -> ExtractedG2 -> S.Set L.Name -> Seq.Seq L.Name -> m (NameMap, TypeNameMap, ExtractedG2)
setUpImports nm tm env ex_g2 prev_explored rel_names = do
    (imports_exg2, (imports_nm, import_tnm)) <- SM.runStateT (loadImports env (exg2_binds ex_g2) prev_explored rel_names) (nm, tm)
    let adj_funcs_exg2 = adjustFunctions imports_nm imports_exg2

    let merged_exg2 = mergeExtractedG2s [ex_g2, adj_funcs_exg2]
        injected_exg2 = specialInject merged_exg2
    liftIO $ writeIORef compiledModules $ Just (merged_exg2, imports_nm, import_tnm, prev_explored)
    return (imports_nm, import_tnm, injected_exg2)

-- Based on https://dl.acm.org/doi/pdf/10.1145/3495272
loadImports :: SM.MonadIO m => HscEnv -> HM.HashMap L.Name L.Expr -> S.Set L.Name -> Seq.Seq L.Name -> NamesT m ExtractedG2
loadImports env local_binds prev_explored ns = do
    external_package_state <- liftIO $ hscEPS env
    let all_ids = nonDetNameEnvElts $ eps_PTE external_package_state
        all_tys = mapMaybe (\case
                                ATyCon t -> Just t
                                _ -> Nothing) all_ids
        all_imp_binds = mapMaybe (\case
                                        AnId i -> fmap (i,) . maybeUnfoldingTemplate $ realIdUnfolding i
                                        _ -> Nothing) all_ids

    -- liftIO . print . nub . map L.nameModule $ map (mkName . varName . fst) all_imp_binds

    -- Compute bindings. The total number of binds is (very) large. As an optimization, we only convert binds
    -- that are actually relevant to the function(s) we are symbolically executing.
    rel_binds <- convertRelBinds local_binds all_imp_binds prev_explored (S.fromList $ F.toList ns) []
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
                -> S.Set L.Name -- ^ Previously explored/loaded names
                -> S.Set L.Name -- ^ Relevant names
                -> [(GHC.Id, CoreExpr)]
                -> NamesT m [(GHC.Id, CoreExpr)]
convertRelBinds local_binds binds = go
    where
        go _ to_explore rel | S.null to_explore = return rel
        go explored to_explore so_far_rel
            | n `notElem` explored = do
                -- Find relevent bindings from the imports
                rel_binds <- filterM (\(i, _) -> liftM2 (==) (valNameLookup $ varName i) (return n)) binds
                let n_rel_call = S.toList . mconcat $ map (relVar . snd) rel_binds
                n_rel_call_g2 <- mapM (valNameLookup . varName) n_rel_call

                -- Find relevant local bindings to search deeper for needed imports
                let local_names = maybe S.empty topVarNames $ HM.lookup n local_binds
                -- liftIO . putStrLn $ "n = " ++ show n ++  "     local = " ++ show (length local_names) ++ "     ns = " ++ show (length ns)

                let ns' = ((S.fromList n_rel_call_g2 <> local_names) `S.difference` explored) <> ns
                    explored' = S.insert n explored
                go explored' ns' (rel_binds ++ so_far_rel)
            | otherwise = go explored ns so_far_rel
            where
                (n, ns) = fromJust $ S.minView to_explore

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

adjustFunctions :: NameMap -> ExtractedG2 -> ExtractedG2
adjustFunctions nm ex_g2 = do
      adjustFunction ("pSmtLen#", Just "G2.Plugin.Prim") nm (callPrim nm "strLen#")
    . adjustFunction ("pSmtAppend#", Just "G2.Plugin.Prim") nm (callPrim nm "strAppend#")
    . adjustFunction ("pIsSMTRep#", Just "G2.Plugin.Prim") nm (callPrim nm "isSMTRep#")
    . adjustAssert "assert" "G2.Plugin" nm
    $ adjustAssume (Just "G2.Plugin") nm ex_g2

callPrim :: NameMap -> TX.Text -> L.Expr 
callPrim nm n =
    case HM.lookup (n, Just "GHC.Prim") nm of
        Just prim_n -> L.Var (Id prim_n TyUnknown)
        Nothing -> error "callPrim: primitive not found"

------------------------------------------------------------------------------
-- Functions for use in plugins
------------------------------------------------------------------------------
smtLen :: [a] -> Int
smtLen xs = xs `evalSeq` I# (pSmtLen# xs)

(+++) :: [a] -> [a] -> [a]
(+++) = smtAppend

smtAppend :: [a] -> [a] -> [a]
smtAppend xs ys = xs `evalSeq` ys `evalSeq` pSmtAppend# xs ys

{-# NOINLINE evalSeq #-}
evalSeq :: [a] -> b -> b
evalSeq xs b = evalSeq' xs `seq` b

evalSeq' :: [a] -> [a]
evalSeq' xs = go xs
  where
    go ys | pIsSMTRep# ys = ys
    go !ys | pIsSMTRep# ys = ys
    go [] = []
    go ((!y):ys) = y:go ys

-- Equivalence Checking
tryMaybe :: IO a -> IO (Maybe a)
tryMaybe a = Ex.catch (a >>= \v -> return (Just v)) (\(_ :: Ex.SomeException) -> return Nothing)

tryMaybeUnsafe :: a -> Maybe a
tryMaybeUnsafe x = unsafePerformIO $ tryMaybe (let !y = x in return y)

comp :: Eq a => a -> a -> a
comp real_def smt_def = 
    let b = tryMaybeUnsafe smt_def == tryMaybeUnsafe real_def in G2.Plugin.assert b real_def