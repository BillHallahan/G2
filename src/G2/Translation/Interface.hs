module G2.Translation.Interface
  ( translateLoaded
  , translateLoadedD
  , translateLoadedBigBase
  ) where

import DynFlags

import Data.List
import Data.Maybe
import qualified Data.Text as T
import qualified Data.HashMap.Lazy as HM

import System.FilePath


import G2.Config
import G2.Language
import G2.Translation.Haskell
import G2.Translation.InjectSpecials
import G2.Translation.PrimInject
import G2.Translation.TransTypes



translateLibs :: NameMap -> TypeNameMap -> TranslationConfig -> Maybe HscTarget -> [FilePath]
    -> IO (ExtractedG2, NameMap, TypeNameMap)
translateLibs nm tm tr_con hsc fs = translateLibs' nm tm tr_con emptyExtractedG2 hsc fs

translateLibs' :: NameMap -> TypeNameMap -> TranslationConfig -> ExtractedG2 -> Maybe HscTarget -> [FilePath]
    -> IO (ExtractedG2, NameMap, TypeNameMap)
translateLibs' nm tnm _ exg2 _ [] = return (exg2, nm, tnm)
translateLibs' nm tnm tr_con extg2 hsc (f:fs) = do
  let guess_dir = dropWhileEnd (/= '/') f
  (new_nm, new_tnm, extg2') <- hskToG2ViaCgGutsFromFile hsc guess_dir f nm tnm tr_con
  translateLibs' new_nm new_tnm tr_con (mergeExtractedG2s [extg2, extg2']) hsc fs

-- The version of translateLoaded that we should be using
translateLoaded :: FilePath -> FilePath -> [FilePath] -> TranslationConfig -> Config
                 -> IO (Maybe T.Text, ExtractedG2)
translateLoaded proj src libs tr_con config = do
  (base_exg2, b_nm, b_tnm) <- translateLibs specialConstructors specialTypeNames tr_con Nothing (base config)
  let base_prog = [exg2_binds base_exg2]
      base_tys = exg2_tycons base_exg2
      b_exp = exg2_exports base_exg2

  (lib_transs, lib_nm, lib_tnm) <- translateLibs b_nm b_tnm tr_con (Just HscInterpreted) libs
  let lib_exp = exg2_exports lib_transs

  let base_tys' = base_tys ++ specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  let base_trans' = base_exg2 { exg2_binds = concat base_prog', exg2_tycons = base_tys' }

  let merged_lib = mergeExtractedG2s ([base_trans', lib_transs])

  -- Now the stuff with the actual target
  (_, _, exg2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) proj src lib_nm lib_tnm tr_con
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

-- Soon to be deprecated
translateLoadedD :: FilePath -> FilePath -> [FilePath] -> TranslationConfig -> Config -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name])
translateLoadedD proj src libs tr_con config = do
  -- Read the extracted libs and merge them
  -- Recall that each of these files comes with NameMap and TypeNameMap
  (nm, tnm, libs_g2) <- mapM readFileExtractedG2 libs >>= return . mergeFileExtractedG2s

  -- Now do the target file
  (nm2, tnm2, tgt_g2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) proj src nm tnm tr_con

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

-- The version of translateLoaded that is supposed to handle the dumped base
translateLoadedBigBase ::
    FilePath
    -> FilePath
    -> [FilePath]
    -> TranslationConfig
    -> Config
    -> IO (Maybe T.Text, ExtractedG2)
translateLoadedBigBase proj src libs transConfig config = do
  {- Big picture steps:
      1. Recursively read in all the G2 dumps of base via readAllExtracedG2s
      2. Hope that we can just Map.union the NameMap and TypeNameMap together
      3. Merge ExtractedG2s naively (via (++), akin to the union operation)
      4. Do translation for all the external libraries
        4a. Specifically modify GHC notions of Primitives to G2's via priminject
      5. Merge base and external libraries
      6. Run hskToG2 using the new union'd NameMap and TypeNameMap
      7. absVarLoc
      8. Done
  -}

  -- The stuff with base and merging
  {-
    allDumpTriples <- readAllExtractedG2s
                        (head $ base config)
                        ((head $ base config) ++ "/Prelude.g2-dump") 
  -}
  base1Exs <- readAllExtractedG2s "../base-dumps/" "Prelude.g2-dump"
  -- base2Exs <- readAllExtractedG2s "../base-dumps/" "Control.Exception.Base.g2-dump"
  -- let (baseNameMap, baseTypeNameMap, baseExG2) = mergeFileExtractedG2s (base1Exs ++ base2Exs)
  let (baseNameMap, baseTypeNameMap, baseExG2) = mergeFileExtractedG2s (base1Exs)

  putStrLn "translateLoadedBigBase relevant base stuff:"
  mapM_ (putStrLn . T.unpack) $ exg2_mod_names baseExG2

  -- External library translation
  (libExG2, libNameMap, libTypeNameMap)
    <- translateLibs
        baseNameMap
            -- (HM.union baseNameMap specialConstructors)
        baseTypeNameMap
            -- (HM.union baseTypeNameMap specialTypeNames)
        transConfig (Just HscInterpreted) libs

  -- Replacing GHC's notion of primitives and what not with G2's
  let baseTys' = (exg2_tycons baseExG2) ++ specialTypes
  let baseProg' = addPrimsToBase baseTys' [exg2_binds baseExG2]
  let baseExG2' = baseExG2 { exg2_binds = concat baseProg', exg2_tycons = baseTys' }

  let postPrimExG2 = mergeExtractedG2s ([baseExG2', libExG2])

  -- Load the actual target, with baseNameMap and baseTypeNameMap
  (_, _, tgtExG2)
    <- hskToG2ViaCgGutsFromFile
        (Just HscInterpreted)
        proj
        src
        baseNameMap
        baseTypeNameMap transConfig
  
  let tgtModName = listToMaybe $ exg2_mod_names tgtExG2
  let tgtExports = exg2_exports tgtExG2

  -- Merge target ExtractedG2 into the postPrim (base ++ lib) that already exists
  let mergedExG2 = mergeExtractedG2s [tgtExG2, postPrimExG2]
      merged_prog = [exg2_binds mergedExG2]
      merged_tys = exg2_tycons mergedExG2
      merged_cls = exg2_classes mergedExG2

  -- final injection phase
  let (near_final_prog, final_tys) = primInject $ dataInject merged_prog merged_tys

  let final_merged_cls = primInject merged_cls

  final_prog <- absVarLoc near_final_prog

  let final_exg2 = mergedExG2 { exg2_binds = concat final_prog
                              , exg2_tycons = final_tys
                              , exg2_classes = final_merged_cls
                              , exg2_exports = (exg2_exports baseExG2) ++
                                               (exg2_exports libExG2) ++
                                               (exg2_exports tgtExG2) }
                              
  return (tgtModName, final_exg2)



