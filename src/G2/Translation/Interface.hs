module G2.Translation.Interface ( translateLoaded ) where

import DynFlags

import Control.Monad.Extra
import Data.List
import Data.Maybe
import qualified Data.Text as T
import System.Directory

import G2.Config
import G2.Language
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

  translateLibPairs specialConstructors specialTypeNames tr_con config emptyExtractedG2 hsc base_inc bases


translateLibs :: NameMap
  -> TypeNameMap
  -> TranslationConfig
  -> Config
  -> Maybe HscTarget
  -> [FilePath]
  -> IO (ExtractedG2, NameMap, TypeNameMap)
translateLibs nm tm tr_con config hsc fs = do
  -- If we are not given anything, then we have to guess the project
  let inc = map (dropWhileEnd (/= '/')) fs
  translateLibPairs nm tm tr_con config emptyExtractedG2 hsc inc fs


translateLibPairs :: NameMap
  -> TypeNameMap
  -> TranslationConfig
  -> Config
  -> ExtractedG2
  -> Maybe HscTarget
  -> [IncludePath]
  -> [FilePath]
  -> IO (ExtractedG2, NameMap, TypeNameMap)
translateLibPairs nm tnm _ _ exg2 _ _ [] = return (exg2, nm, tnm)
translateLibPairs nm tnm tr_con config exg2 hsc inc_paths (f: fs) = do
  (new_nm, new_tnm, exg2') <- hskToG2ViaCgGutsFromFile hsc inc_paths [f] nm tnm tr_con
  translateLibPairs new_nm new_tnm tr_con config (mergeExtractedG2s [exg2, exg2']) hsc inc_paths fs

translateLoaded :: [FilePath]
  -> [FilePath]
  -> [FilePath]
  -> TranslationConfig
  -> Config
  -> IO (Maybe T.Text, ExtractedG2)
translateLoaded proj src libs tr_con config = do
  -- Stuff with the actual target
  let def_proj = extraDefaultInclude config
  tar_ems <- envModSumModGuts (Just HscInterpreted) (def_proj ++ proj) src tr_con
  let imports = envModSumModGutsImports tar_ems
  extra_imp <- return . catMaybes =<< mapM (findImports (baseInclude config)) imports

  -- Stuff with the base library
  (base_exg2, b_nm, b_tnm) <- translateBase tr_con config extra_imp Nothing
  let base_prog = exg2_binds base_exg2
      base_tys = exg2_tycons base_exg2
      b_exp = exg2_exports base_exg2


  (lib_transs, lib_nm, lib_tnm) <- translateLibs b_nm b_tnm tr_con config (Just HscInterpreted) libs
  let lib_exp = exg2_exports lib_transs

  let base_tys' = base_tys ++ specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  let base_trans' = base_exg2 { exg2_binds = base_prog', exg2_tycons = base_tys' }

  let merged_lib = mergeExtractedG2s ([base_trans', lib_transs])

  -- Now the stuff with the actual target
  (_, _, exg2) <- hskToG2ViaEMS tr_con tar_ems lib_nm lib_tnm
  let mb_modname = lookup (head src) $ exg2_mod_names exg2
  let h_exp = exg2_exports exg2

  -- putStrLn $ "exg2_deps = " ++ show (exg2_deps exg2)

  let merged_exg2 = mergeExtractedG2s [exg2, merged_lib]
      merged_prog = exg2_binds merged_exg2
      merged_tys = exg2_tycons merged_exg2
      merged_cls = exg2_classes merged_exg2

  -- final injection phase
  let (near_final_prog, final_tys, final_rules) = primInject $ dataInject (merged_prog, merged_tys, exg2_rules merged_exg2) merged_tys

  let final_merged_cls = primInject merged_cls

  final_prog <- absVarLoc near_final_prog

  let final_exg2 = merged_exg2 { exg2_binds = final_prog
                               , exg2_tycons = final_tys
                               , exg2_classes = final_merged_cls
                               , exg2_exports = b_exp ++ lib_exp ++ h_exp
                               , exg2_rules = final_rules}

  return (mb_modname, final_exg2)

findImports :: [FilePath] -> FilePath -> IO (Maybe FilePath)
findImports roots fp = do
    let fp' = map (\c -> if c == '.' then '/' else c) fp
    mr <- findM (\r -> doesFileExist $ r ++ fp' ++ ".hs") roots
    case mr of
        Just r -> return . Just $ r ++ fp' ++ ".hs"
        Nothing -> return Nothing
