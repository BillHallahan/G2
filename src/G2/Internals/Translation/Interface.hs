module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimInject

translationPrimDefs :: FilePath -> FilePath -> FilePath
                    -> IO (Program, [ProgramType])
translationPrimDefs proj src primsF = do
    (data_prog, prog_tys) <- hskToG2 proj src

    prims <- mkPrims primsF
    let prim_prog = mergeProgs data_prog prims
    return . primInject $ dataInject prim_prog prog_tys

translation :: FilePath -> FilePath -> IO (Program, [ProgramType])
translation = hskToG2



prepBase :: FilePath -> IO ()
prepBase destination = do
    putStrLn $ "Downloading base to " ++ destination
    downloadBase destination
    putStrLn $ "Unpacking " ++ destination
    unpackTarSameDir destination

