module G2.Internals.Translation.Interface where

import Data.List

import G2.Internals.Language
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.InjectSpecials
import G2.Internals.Translation.PrimInject

translateLoaded :: FilePath -> FilePath -> FilePath -> Bool
                -> IO (Program, [ProgramType], [(Name, Id, [Id])])
translateLoaded proj src prelude simpl = do
    let basedir = dropWhileEnd (/= '/') prelude
    (data_prog, prog_tys, prog_cls) <- hskToG2 proj src simpl
    -- prims <- mkPrims primsF
    (base_prog, base_tys, base_cls) <- hskToG2 basedir prelude simpl

    let merged_prog = mergeProgs data_prog base_prog

    let (merged_prog', merged_prog_tys) =
            mergeProgTys merged_prog merged_prog prog_tys base_tys
    let (merged_prog2', prog_tys') = injectSpecials merged_prog_tys merged_prog'

    let merged_classes = prog_cls ++ base_cls

    let (fin_prog, fin_tys) = primInject $ dataInject merged_prog2' prog_tys'

    let classes = mergeTCs merged_classes fin_prog

    return (fin_prog, fin_tys, classes)

translation :: FilePath -> FilePath -> Bool -> IO (Program, [ProgramType], [(Name, Id, [Id])])
translation = hskToG2

prepBase :: FilePath -> IO ()
prepBase destination = do
    putStrLn $ "Downloading base to " ++ destination
    downloadBase destination
    putStrLn $ "Unpacking " ++ destination
    unpackTarSameDir destination

