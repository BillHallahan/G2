module G2.Internals.Translation.Interface where

import Data.List
import qualified Data.Text as T

import G2.Internals.Language
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.InjectSpecials
import G2.Internals.Translation.PrimInject

import Data.Maybe

translateLibs :: [FilePath] -> NameMap -> TypeNameMap -> Bool -> IO ([(Program, [ProgramType], [(Name, Id, [Id])])], NameMap, TypeNameMap)
translateLibs [] nm tnm _ = return ([], nm, tnm)
translateLibs (f:fs) nm tnm simpl = do
  (others, others_nm, others_tnm) <- translateLibs fs nm tnm simpl
  let guess_dir = dropWhileEnd (/= '/') f
  (_, prog, tys, cls, new_nm, new_tnm) <- hskToG2 guess_dir f others_nm others_tnm simpl
  return $ ((prog, tys, cls) : others, new_nm, new_tnm)

mergeTranslates :: [(Program, [ProgramType], [(Name, Id, [Id])])] -> (Program, [ProgramType], [(Name, Id, [Id])])
mergeTranslates [] = error "mergeTranslates: nothing to merge!"
mergeTranslates (t:[]) = t
mergeTranslates ((prog, tys, cls):ts) =
  let (m_prog, m_tys, m_cls) = mergeTranslates ts
      prog0 = mergeProgs m_prog prog
      (prog1, tys1) = mergeProgTys prog0 prog0 m_tys tys
      cls1 = cls ++ m_cls
  in (prog1, tys1, cls1)

translateLoaded :: FilePath -> FilePath -> FilePath -> Bool -> Maybe FilePath
                -> IO (T.Text, Program, [ProgramType], [(Name, Id, [Id])])
translateLoaded proj src prelude simpl m_mapsrc = do
  (tgt_name, final_prog, final_tys, classes, _) <- translateLoadedV proj src prelude simpl (maybeToList m_mapsrc)
  return (tgt_name, final_prog, final_tys, classes)

translateLoadedV :: FilePath -> FilePath -> FilePath -> Bool -> [FilePath]
                -> IO (T.Text, Program, [ProgramType], [(Name, Id, [Id])], [T.Text])
translateLoadedV proj src prelude simpl libs = do
  ((base_prog, base_tys, base_cls), b_nm, b_tnm) <-
      (\(bs, base_nm, base_tnm) -> return (head bs, base_nm, base_tnm)) =<<
      translateLibs [prelude] specialConstructors specialTypeNames simpl
  (lib_transs, lib_nm, lib_tnm) <- translateLibs libs b_nm b_tnm simpl

  let base_prog' = addPrimsToBase base_prog
  let base_tys' = base_tys ++ specialTypes
  let base_trans' = (base_prog', base_tys', base_cls)

  let merged_lib = mergeTranslates (base_trans' : lib_transs)

  -- Now the stuff with the actual target
  (tgt_name, tgt_prog, tgt_tys, tgt_cls, _, _) <- hskToG2 proj src lib_nm lib_tnm simpl
  let tgt_trans = (tgt_prog, tgt_tys, tgt_cls)
  let (merged_prog, merged_tys, merged_cls) = mergeTranslates [tgt_trans, merged_lib]

  -- final injection phase
  let (final_prog, final_tys) = primInject $ dataInject merged_prog merged_tys
  let final_cls = mergeTCs merged_cls merged_prog

  return (T.pack tgt_name, final_prog, final_tys, final_cls, [])
  

