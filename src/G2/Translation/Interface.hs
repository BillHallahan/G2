module G2.Translation.Interface ( translateLoaded
                                , translateLoadedD ) where

import DynFlags

import Data.List
import Data.Maybe
import qualified Data.Text as T

import G2.Config
import G2.Language
import G2.Translation.Haskell
import G2.Translation.InjectSpecials
import G2.Translation.PrimInject
import G2.Translation.TransTypes


translateBase :: TranslationConfig
  -> Config
  -> Maybe HscTarget
  -> IO (ExtractedG2, NameMap, TypeNameMap)
translateBase tr_con config hsc = do
  -- For base we have the advantage of knowing apriori the structure
  -- So we can list the (proj, file) pairings
  let base_inc = baseInclude config
  let bases = base config

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
  (new_nm, new_tnm, exg2') <- hskToG2ViaCgGutsFromFile hsc inc_paths [f] nm tnm tr_con config
  translateLibPairs new_nm new_tnm tr_con config (mergeExtractedG2s [exg2, exg2']) hsc inc_paths fs

translateLoaded :: [FilePath]
  -> [FilePath]
  -> [FilePath]
  -> TranslationConfig
  -> Config
  -> IO (Maybe T.Text, ExtractedG2)
translateLoaded proj src libs tr_con config = do
  (base_exg2, b_nm, b_tnm) <- translateBase tr_con config Nothing
  let base_prog = [exg2_binds base_exg2]
      base_tys = exg2_tycons base_exg2
      b_exp = exg2_exports base_exg2

  (lib_transs, lib_nm, lib_tnm) <- translateLibs b_nm b_tnm tr_con config (Just HscInterpreted) libs
  let lib_exp = exg2_exports lib_transs

  let base_tys' = base_tys ++ specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  let base_trans' = base_exg2 { exg2_binds = concat base_prog', exg2_tycons = base_tys' }

  let merged_lib = mergeExtractedG2s ([base_trans', lib_transs])

  -- Now the stuff with the actual target
  let def_proj = extraDefaultInclude config
      def_src = extraDefaultMods config
  (_, _, exg2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) (def_proj ++ proj) (def_src ++ src) lib_nm lib_tnm tr_con config
  let mb_modname = listToMaybe $ exg2_mod_names exg2
  let h_exp = exg2_exports exg2

  let merged_exg2 = mergeExtractedG2s [exg2, merged_lib]
      merged_prog = [exg2_binds merged_exg2]
      merged_tys = exg2_tycons merged_exg2
      merged_cls = exg2_classes merged_exg2

  -- final injection phase
  let (near_final_prog, final_tys) = primInject $ dataInject merged_prog merged_tys

  let final_merged_cls = primInject merged_cls

  final_prog <- absVarLoc near_final_prog

  let final_exg2 = merged_exg2 { exg2_binds = concat final_prog
                               , exg2_tycons = final_tys
                               , exg2_classes = final_merged_cls
                               , exg2_exports = b_exp ++ lib_exp ++ h_exp}

  return (mb_modname, final_exg2)

translateLoadedD :: [FilePath]
  -> [FilePath]
  -> [FilePath]
  -> TranslationConfig
  -> Config
  -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name])
translateLoadedD proj src libs tr_con config = do
  -- Read the extracted libs and merge them
  -- Recall that each of these files comes with NameMap and TypeNameMap
  (nm, tnm, libs_g2) <- mapM readFileExtractedG2 libs >>= return . mergeFileExtractedG2s

  -- Now do the target file
  (nm2, tnm2, tgt_g2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) proj src nm tnm tr_con config

  -- Combine the library g2 and extracted g2s
  -- Also do absVarLoc!
  let almost_g2 = mergeExtractedG2s [libs_g2, tgt_g2]
  let almost_prog = [exg2_binds almost_g2]

  -- Inject the primitive stuff
  let final_classes = primInject $ exg2_classes almost_g2
  let (pre_prog, final_tycons) = primInject $ dataInject almost_prog $ exg2_tycons almost_g2

  final_prog <- absVarLoc pre_prog

  let name = listToMaybe $ exg2_mod_names tgt_g2
  let exports = exg2_exports almost_g2

  return (name,
          final_prog,
          final_tycons,
          final_classes,
          exports)

