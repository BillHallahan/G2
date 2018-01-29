module G2.Internals.Translation.Interface where

import Data.List

import G2.Internals.Language
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.InjectSpecials
import G2.Internals.Translation.PrimInject

translateLoaded :: FilePath -> FilePath -> FilePath -> Bool -> Maybe FilePath
                -> IO (String, Program, [ProgramType], [(Name, Id, [Id])])
translateLoaded proj src prelude simpl m_mapsrc = do
    let basedir = dropWhileEnd (/= '/') prelude
    (tgt_name, data_prog, prog_tys, prog_cls) <- hskToG2 proj src simpl

    -- print data_prog
    -- prims <- mkPrims primsF
    (base_name, base_prog, base_tys, base_cls) <- hskToG2 basedir prelude simpl

    (map_prog, map_tys, map_cls) <- case m_mapsrc of
        Nothing -> return ([], [], [])
        Just mapsrc -> do
          let mapdir = dropWhileEnd (/= '/') mapsrc
          (_, map_prog, map_tys, map_cls) <- hskToG2 mapdir mapsrc simpl
          return (map_prog, map_tys, map_cls)


    let lib_prog = base_prog ++ map_prog
    let lib_tys = base_tys ++ map_tys
    let lib_cls = base_cls ++ map_cls

    -- mapM_ print data_prog
    -- putStrLn "&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&"
    -- mapM_ print base_prog


    -- print $ data_prog
    -- print $ base_prog

    let merged_prog = mergeProgs data_prog lib_prog

    -- putStrLn "-------"
    -- mapM_ print merged_prog
    -- error "NOOO"

    let (merged_prog', merged_prog_tys) =
            mergeProgTys merged_prog merged_prog prog_tys lib_tys
    let (merged_prog2', prog_tys') = injectSpecials merged_prog_tys merged_prog'

    -- print merged_prog_tys

    -- print prog_tys'

    let merged_classes = prog_cls ++ lib_cls

    let (fin_prog, fin_tys) = primInject $ dataInject merged_prog2' prog_tys'


    let classes = mergeTCs merged_classes fin_prog

    return (tgt_name, fin_prog, fin_tys, classes)

translation :: FilePath -> FilePath -> Bool -> IO (String, Program, [ProgramType], [(Name, Id, [Id])])
translation = hskToG2

prepBase :: FilePath -> IO ()
prepBase destination = do
    putStrLn $ "Downloading base to " ++ destination
    downloadBase destination
    putStrLn $ "Unpacking " ++ destination
    unpackTarSameDir destination

