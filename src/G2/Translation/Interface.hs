{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Translation.Interface ( translateBase
                                , translateLoaded
                                , specialInject
                                , dirPath) where

import Control.Monad.Extra
import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified Data.Text as T
import System.Directory

import G2.Config
import G2.Language as G2
import G2.Translation.GHC
import G2.Translation.Haskell
import G2.Translation.InjectSpecials
import G2.Translation.PrimInject
import G2.Translation.TransTypes

translateBase :: TranslationConfig
  -> Config
  -> [FilePath]
  -> Maybe HscTarget
  -> IO (ExtractedG2, NameMap, TypeNameMap)
translateBase tr_con config extra hsc = do
  -- For base we have the advantage of knowing apriori the structure
  -- So we can list the (proj, file) pairings
  let base_inc = baseInclude config
  let bases = nub $ base config ++ extra

  (base_exg2, b_nm, b_tnm) <- translateLibPairs specialConstructors specialTypeNames tr_con emptyExtractedG2 hsc base_inc bases

  let base_prog = exg2_binds base_exg2
      base_tys = exg2_tycons base_exg2

  let base_tys' = base_tys `HM.union` specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  return (base_exg2 { exg2_binds = base_prog', exg2_tycons = base_tys' }, b_nm, b_tnm)

translateLibPairs :: NameMap
  -> TypeNameMap
  -> TranslationConfig
  -> ExtractedG2
  -> Maybe HscTarget
  -> [IncludePath]
  -> [FilePath]
  -> IO (ExtractedG2, NameMap, TypeNameMap)
translateLibPairs nm tnm _ exg2 _ _ [] = return (exg2, nm, tnm)
translateLibPairs nm tnm tr_con exg2 hsc inc_paths (f: fs) = do
  (new_nm, new_tnm, exg2') <- hskToG2ViaCgGutsFromFile hsc inc_paths [f] nm tnm tr_con
  translateLibPairs new_nm new_tnm tr_con (mergeExtractedG2s [exg2, exg2']) hsc inc_paths fs

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
selectBackend :: TranslationConfig -> Maybe Backend
selectBackend tr | interpreter tr = Just interpreterBackend
selectBackend _ = Just noBackend
#elif MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
selectBackend :: TranslationConfig -> Maybe Backend
selectBackend tr | interpreter tr = Just Interpreter
selectBackend _ = Just NoBackend
#else
selectBackend :: TranslationConfig -> Maybe HscTarget
selectBackend tr | interpreter tr = Just HscInterpreted
selectBackend _ = Just HscNothing
#endif

translateLoaded :: [FilePath]
  -> [FilePath]
  -> TranslationConfig
  -> Config
  -> IO ([Maybe T.Text], ExtractedG2)
translateLoaded proj src tr_con config = do
  let tr_con' = tr_con { hpc_ticks = hpc config || search_strat config == Subpath || hpc_discard_strat config }
  -- Stuff with the actual target
  let def_proj = extraDefaultInclude config
  tar_ems <- envModSumModGutsFromFile (selectBackend tr_con') (def_proj ++ proj ++ map dirPath src) src tr_con' 
  let imports = envModSumModGutsImports tar_ems
  extra_imp <- return . catMaybes =<< mapM (findImports (baseInclude config)) imports

  -- Stuff with the base library
  (base_exg2, b_nm, b_tnm) <- translateBase tr_con' config extra_imp Nothing

  -- Now the stuff with the actual target
  (f_nm, f_tm, exg2) <- hskToG2ViaEMS tr_con'  tar_ems b_nm b_tnm
  let mb_modname = exg2_mod_names exg2
  let exg2' = adjustAssertG2Symbolic f_nm
            . adjustAssertGHC f_nm
            . adjustAssume (Just "GHC.Prim") f_nm
            . adjustAssume (Just "G2.Symbolic") f_nm
            . adjustMkSymbolicPrim SNoLog "symgen" (Just "GHC.Prim") f_nm
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
            $ adjustMkSymbolicPrim SLog "symgen_G2_INTERNAL" Nothing f_nm exg2
#else
            $ adjustMkSymbolicPrim SLog "symgen_G2_INTERNAL" (Just "G2.Symbolic") f_nm exg2
#endif

  let merged_exg2 = mergeExtractedG2s [exg2', base_exg2]
  let injected_exg2@ExtractedG2 { exg2_binds = near_final_prog } = specialInject merged_exg2

  final_prog <- absVarLoc near_final_prog

  let final_exg2 = injected_exg2 { exg2_binds = final_prog }

  return (mb_modname, final_exg2)

adjustMkSymbolicPrim :: SymLog -> T.Text -> Maybe T.Text -> NameMap -> ExtractedG2 -> ExtractedG2
adjustMkSymbolicPrim sym_log occ_n md_nm nm exg2 =
    let
        n = (occ_n, md_nm)
    in
    adjustFunction n nm exg2
            (let a = Id (Name "a" Nothing 0 Nothing) TYPE in G2.Lam TypeL a (SymGen sym_log $ TyVar a))

adjustAssume :: Maybe T.Text -> NameMap -> ExtractedG2 -> ExtractedG2
adjustAssume mdl nm exg2 =
    adjustFunction ("assume", mdl) nm exg2
            (let a = Id (Name "a" Nothing 0 Nothing) TYPE
                 b = Id (Name "b" Nothing 0 Nothing) TyUnknown
                 x = Id (Name "x" Nothing 0 Nothing) (TyVar a) in
                G2.Lam TypeL a . G2.Lam TermL b . G2.Lam TermL x $ G2.Assume Nothing (G2.Var b) (G2.Var x))

adjustAssertG2Symbolic :: NameMap -> ExtractedG2 -> ExtractedG2
adjustAssertG2Symbolic = adjustAssert "assert" "G2.Symbolic"

adjustAssertGHC :: NameMap -> ExtractedG2 -> ExtractedG2
adjustAssertGHC = adjustAssert "assert" "GHC.Base"

adjustAssert :: T.Text -> T.Text -> NameMap -> ExtractedG2 -> ExtractedG2
adjustAssert f m nm exg2 =
    adjustFunction (f, Just m) nm exg2
            (let a = Id (Name "a" Nothing 0 Nothing) TYPE
                 b = Id (Name "b" Nothing 0 Nothing) TyUnknown
                 x = Id (Name "x" Nothing 0 Nothing) (TyVar a) in
                G2.Lam TypeL a . G2.Lam TermL b . G2.Lam TermL x $ G2.Assert Nothing (G2.Var b) (G2.Var x))

adjustFunction :: (T.Text, Maybe T.Text) -> NameMap -> ExtractedG2 -> G2.Expr -> ExtractedG2
adjustFunction fname@(_, Just _) nm exg2@(ExtractedG2 { exg2_binds = binds}) e =
    case HM.lookup fname nm of
        Just sym_n -> exg2 { exg2_binds = HM.insert sym_n e binds }
        Nothing -> exg2
adjustFunction (n, Nothing) nm exg2@(ExtractedG2 { exg2_binds = binds}) e =
    case find (\b -> nameOcc b == n) (HM.keys binds) of
        Just sym_n -> exg2 { exg2_binds = HM.insert sym_n e binds }
        Nothing -> exg2

specialInject :: ExtractedG2 -> ExtractedG2
specialInject exg2 =
    let
        prog = exg2_binds exg2
        tys = exg2_tycons exg2
        rules = exg2_rules exg2
        cls = exg2_classes exg2
    
        (prog', tys', rules') = primInject $ dataInject (prog, tys, rules) tys
        cls' = primInject cls
    in
    exg2 { exg2_binds = prog'
         , exg2_tycons = tys'
         , exg2_rules = rules'
         , exg2_classes = cls' }

dirPath :: FilePath -> FilePath
dirPath = reverse . dropWhile (/= '/') . reverse

findImports :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findImports roots fp = do
    let fp' = map (\c -> if c == '.' then '/' else c) fp
    mr <- findM (\r -> doesFileExist $ r ++ fp' ++ ".hs") roots
    case mr of
        Just r -> return . Just $ r ++ fp' ++ ".hs"
        Nothing -> return Nothing
