module G2.Internals.Translation.Interface where

import Data.List
import qualified Data.HashMap.Lazy as HM

import G2.Internals.Language
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.InjectSpecials
import G2.Internals.Translation.PrimInject

translateLoaded :: FilePath -> FilePath -> FilePath -> Bool -> Maybe FilePath
                -> IO (String, Program, [ProgramType], [(Name, Id, [Id])])
translateLoaded proj src prelude simpl m_mapsrc = do
    let basedir = dropWhileEnd (/= '/') prelude
    (base_name, base_prog, base_tys, base_cls, base_nm, base_tm) <- hskToG2 basedir prelude HM.empty HM.empty simpl

    (map_prog, map_tys, map_cls, map_nm, map_tm) <- case m_mapsrc of
        Nothing -> return ([], [], [], base_nm, base_tm)
        Just mapsrc -> do
          let mapdir = dropWhileEnd (/= '/') mapsrc
          (_, map_prog, map_tys, map_cls, map_nm, map_tm) <- hskToG2 mapdir mapsrc base_nm base_tm simpl
          return (map_prog, map_tys, map_cls, map_nm, map_tm)

    (tgt_name, data_prog, prog_tys, prog_cls, _, _) <- hskToG2 proj src map_nm map_tm simpl

    -- print data_prog
    -- prims <- mkPrims primsF

    -- mapM_ print base_prog
    -- mapM_ print map_prog
    -- error "STOPPP"

    let lib_prog0 = mergeProgs base_prog map_prog
    let (lib_prog1, lib_tys) = mergeProgTys lib_prog0 lib_prog0 base_tys map_tys
    let lib_cls = base_cls ++ map_cls

    -- mapM_ print lib_prog1


    let merged_prog0 = mergeProgs data_prog lib_prog1
    let (merged_prog1, merged_tys) = mergeProgTys merged_prog0 merged_prog0 prog_tys lib_tys
    let merged_cls = prog_cls ++ lib_cls

    let (special_prog, special_tys) = injectSpecials merged_tys merged_prog1
    let (final_prog, final_tys) = primInject $ dataInject special_prog special_tys

    let classes = mergeTCs merged_cls merged_prog1


    -- mapM_ print final_prog

    -- error "HALT"

    return (tgt_name, final_prog, final_tys, classes)
    -- return (tgt_name, merged_prog1, merged_tys, classes)

{-

    let lib_prog = base_prog ++ map_prog
    let lib_tys = base_tys ++ map_tys
    let lib_cls = base_cls ++ map_cls

    -- mapM_ print lib_prog
    -- putStrLn "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&"
    -- mapM_ print base_prog

    -- error "STOPPP"

    -- print $ data_prog
    -- print $ base_prog

    let merged_prog = mergeProgs data_prog lib_prog

    -- putStrLn "-------"
    -- mapM_ print merged_prog

    let (merged_prog', merged_prog_tys) =
            mergeProgTys merged_prog merged_prog prog_tys lib_tys
    let (merged_prog2', prog_tys') = injectSpecials merged_prog_tys merged_prog'

    -- mapM_ print merged_prog
    -- error "STOPPP"

    -- print prog_tys'

    let merged_classes = prog_cls ++ lib_cls

    let (fin_prog, fin_tys) = primInject $ dataInject merged_prog2' prog_tys'


    let classes = mergeTCs merged_classes fin_prog

    return (tgt_name, fin_prog, fin_tys, classes)
-}

prepBase :: FilePath -> IO ()
prepBase destination = do
    putStrLn $ "Downloading base to " ++ destination
    downloadBase destination
    putStrLn $ "Unpacking " ++ destination
    unpackTarSameDir destination

