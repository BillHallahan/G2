module G2.Translation.Interface where

import DynFlags

import Data.List
import qualified Data.Text as T

import G2.Config
import G2.Language
import G2.Translation.Haskell
import G2.Translation.InjectSpecials
import G2.Translation.PrimInject

translateLibs :: NameMap -> TypeNameMap -> Bool -> Maybe HscTarget -> [FilePath] -> IO ((Program, [ProgramType], [(Name, Id, [Id])]), NameMap, TypeNameMap, [Name])
translateLibs nm tm simpl hsc fs = translateLibs' nm tm simpl ([], [], []) hsc fs []

translateLibs' :: NameMap -> TypeNameMap -> Bool -> (Program, [ProgramType], [(Name, Id, [Id])]) -> Maybe HscTarget -> [FilePath] -> [Name] -> IO ((Program, [ProgramType], [(Name, Id, [Id])]), NameMap, TypeNameMap, [Name])
translateLibs' nm tnm _ pptn _ [] ex = return (pptn, nm, tnm, ex)
translateLibs' nm tnm simpl (prog, tys, cls) hsc (f:fs) ex = do
  let guess_dir = dropWhileEnd (/= '/') f
  (_, n_prog, n_tys, n_cls, new_nm, new_tnm, _, ex') <- hskToG2 hsc guess_dir f nm tnm simpl
  
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
                -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name], [Name])
translateLoaded proj src libs simpl config = do
  (mb_modname, final_prog, final_tys, classes, target_nm, ex) <- translateLoadedV proj src libs simpl config
  return (mb_modname, final_prog, final_tys, classes, target_nm, ex)

translateLoadedV :: FilePath -> FilePath -> [FilePath] -> Bool -> Config
                 -> IO (Maybe T.Text, Program, [ProgramType], [(Name, Id, [Id])], [Name], [Name])
translateLoadedV proj src libs simpl config = do
  ((base_prog, base_tys, base_cls), b_nm, b_tnm, b_exp) <- translateLibs specialConstructors specialTypeNames simpl Nothing (base config)-- ["../base-4.9.1.0/Control/Exception/Base.hs", base]

  (lib_transs, lib_nm, lib_tnm, lib_exp) <- translateLibs b_nm b_tnm simpl (Just HscInterpreted) libs

  let base_tys' = base_tys ++ specialTypes
  let base_prog' = addPrimsToBase base_tys' base_prog
  let base_trans' = (base_prog', base_tys', base_cls)

  let merged_lib = mergeTranslates ([base_trans', lib_transs])

  -- Now the stuff with the actual target
  (mb_modname, tgt_prog, tgt_tys, tgt_cls, _, _, tgt_lhs, h_exp) <- hskToG2 (Just HscInterpreted) proj src lib_nm lib_tnm simpl
  let tgt_trans = (tgt_prog, tgt_tys, tgt_cls)
  let (merged_prog, merged_tys, merged_cls) = mergeTranslates [tgt_trans, merged_lib]

  let ns = map (idName . fst) $ concat tgt_prog

  -- final injection phase
  -- let (near_final_prog, final_tys) = primInject (merged_prog, merged_tys)
  let (near_final_prog, final_tys) = primInject $ dataInject merged_prog merged_tys

  let final_merged_cls = primInject merged_cls

  final_prog <- absVarLoc near_final_prog

  return (fmap T.pack mb_modname, final_prog, final_tys, final_merged_cls, ns, b_exp ++ lib_exp ++ h_exp)

