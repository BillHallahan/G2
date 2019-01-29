module G2.Translation.Interface where

import DynFlags

import System.Directory

import Data.List
import Data.Maybe
import qualified Data.Text as T

import G2.Config
import G2.Language
import G2.Translation.Haskell
import G2.Translation.InjectSpecials
import G2.Translation.PrimInject
import G2.Translation.TransTypes

translateLibs :: NameMap -> TypeNameMap -> Bool -> Maybe HscTarget -> [FilePath]
    -> IO ((Program, [ProgramType], [(Name, Id, [Id])]), NameMap, TypeNameMap, [Name])
translateLibs nm tm simpl hsc fs = translateLibs' nm tm simpl ([], [], []) hsc fs []

translateLibs' :: NameMap -> TypeNameMap -> Bool -> (Program, [ProgramType], [(Name, Id, [Id])]) -> Maybe HscTarget -> [FilePath] -> [Name]
    -> IO ((Program, [ProgramType], [(Name, Id, [Id])]), NameMap, TypeNameMap, [Name])
translateLibs' nm tnm _ pptn _ [] ex = return (pptn, nm, tnm, ex)
translateLibs' nm tnm simpl (prog, tys, cls) hsc (f:fs) ex = do
  let guess_dir = dropWhileEnd (/= '/') f
  -- (_, n_prog, n_tys, n_cls, new_nm, new_tnm, ex') <- hskToG2FromFile hsc guess_dir f nm tnm simpl
  -- (new_nm, new_tnm, exg2) <- hskToG2ViaModGutsFromFile hsc guess_dir f nm tnm simpl
  (new_nm, new_tnm, exg2) <- hskToG2ViaCgGutsFromFile hsc guess_dir f nm tnm simpl
  let n_prog = [exg2_binds exg2]
  let n_tys = exg2_tycons exg2
  let n_cls = exg2_classes exg2
  let ex' = exg2_exports exg2

  translateLibs' new_nm new_tnm simpl (prog ++ n_prog, tys ++ n_tys, cls ++ n_cls) hsc fs (ex ++ ex')
  
mergeTranslates :: [(Program, [ProgramType], [(Name, Id, [Id])])] -> (Program, [ProgramType], [(Name, Id, [Id])])
mergeTranslates [] = error "mergeTranslates: nothing to merge!"
mergeTranslates (t:[]) = t
mergeTranslates ((prog, tys, cls):ts) =
  let (m_prog, m_tys, m_cls) = mergeTranslates ts
      prog' = mergeProgs m_prog prog
      tys1 = mergeProgTys m_tys tys
      cls1 = cls ++ m_cls
  in (prog', tys1, cls1)


translateLoaded :: FilePath -> FilePath -> [FilePath] -> Bool -> Config
                -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name])
translateLoaded proj src libs simpl config = do
  -- (mb_modname, final_prog, final_tys, classes, ex) <- translateLoadedV proj src libs simpl config
  -- let prefix = "/home/celery/foo/yale/dump-base/"
  -- contents <- getDirectoryContents prefix

  -- let libs = map (\c -> prefix ++ c) $ filter (\c -> c /= "." && c /= "..") contents
  -- (mb_modname, final_prog, final_tys, classes, ex) <- translateLoadedD proj src libs simpl config
  (mb_modname, final_prog, final_tys, classes, ex) <- translateLoadedV proj src libs simpl config
  return (mb_modname, final_prog, final_tys, classes, ex)


translateLoadedV :: FilePath -> FilePath -> [FilePath] -> Bool -> Config
                 -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name])
translateLoadedV proj src libs simpl config = do
  ((base_prog, base_tys, base_cls), b_nm, b_tnm, b_exp) <- translateLibs specialConstructors specialTypeNames simpl Nothing (base config)-- ["../base-4.9.1.0/Control/Exception/Base.hs", base]

  (lib_transs, lib_nm, lib_tnm, lib_exp) <- translateLibs b_nm b_tnm simpl (Just HscInterpreted) libs

  let base_tys' = base_tys ++ specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  let base_trans' = (base_prog', base_tys', base_cls)

  let merged_lib = mergeTranslates ([base_trans', lib_transs])

  -- Now the stuff with the actual target
  -- (mb_modname, tgt_prog, tgt_tys, tgt_cls, _, _, h_exp) <- hskToG2FromFile (Just HscInterpreted) proj src lib_nm lib_tnm simpl

  -- (_, _, exg2) <- hskToG2ViaModGutsFromFile (Just HscInterpreted) proj src lib_nm lib_tnm simpl
  (_, _, exg2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) proj src lib_nm lib_tnm simpl
  let mb_modname = listToMaybe $ exg2_mod_names exg2
  let tgt_prog = [exg2_binds exg2]
  let tgt_tys = exg2_tycons exg2
  let tgt_cls = exg2_classes exg2
  let h_exp = exg2_exports exg2


  let tgt_trans = (tgt_prog, tgt_tys, tgt_cls)
  let (merged_prog, merged_tys, merged_cls) = mergeTranslates [tgt_trans, merged_lib]

  -- final injection phase
  -- let (near_final_prog, final_tys) = primInject (merged_prog, merged_tys)
  let (near_final_prog, final_tys) = primInject $ dataInject merged_prog merged_tys

  let final_merged_cls = primInject merged_cls

  final_prog <- absVarLoc near_final_prog

  return (mb_modname, final_prog, final_tys, final_merged_cls, b_exp ++ lib_exp ++ h_exp)


translateLoadedD :: FilePath -> FilePath -> [FilePath] -> Bool -> Config
    -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name])
translateLoadedD proj src libs simpl config = do
  -- Read the extracted libs and merge them
  -- Recall that each of these files comes with NameMap and TypeNameMap
  (nm, tnm, libs_g2) <- mapM readFileExtractedG2 libs >>= return . mergeFileExtractedG2s

  -- Now do the target file
  (nm2, tnm2, tgt_g2) <- hskToG2ViaCgGutsFromFile (Just HscInterpreted) proj src nm tnm simpl

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

