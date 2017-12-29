module G2.Internals.Translation.Interface where

import Data.List

import G2.Internals.Language
import G2.Internals.Translation.Cabal
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.InjectSpecials
import G2.Internals.Translation.PrimInject

translationPrimDefs :: FilePath -> FilePath -> FilePath -> Bool
                    -> IO (Program, [ProgramType])
translationPrimDefs proj src primsF simpl = do
    (data_prog, prog_tys) <- hskToG2 proj src simpl
    -- prims <- mkPrims primsF
    (prims_prog, prims_tys) <- hskToG2 "" primsF simpl
    let merged_prog = mergeProgs data_prog prims_prog
    let (merged_prog', merged_prog_tys) = mergeProgTys merged_prog merged_prog prog_tys prims_tys
    let prog_tys' = injectSpecials merged_prog_tys merged_prog'
    return . primInject $ dataInject merged_prog' prog_tys'

translationBase :: FilePath -> FilePath -> FilePath -> FilePath -> Bool
                -> IO (Program, [ProgramType])
translationBase proj src base prelude simpl = do
    (data_prog, prog_tys) <- hskToG2 proj src simpl
    -- prims <- mkPrims primsF
    (base_prog, base_tys) <- hskToG2 base prelude simpl

    let merged_prog = mergeProgs data_prog base_prog
    let (merged_prog', merged_prog_tys) =
            mergeProgTys merged_prog merged_prog prog_tys base_tys
    let prog_tys' = injectSpecials merged_prog_tys merged_prog'
    let (fin_prog, fin_tys) = primInject $ dataInject merged_prog' prog_tys'

    return (fin_prog, fin_tys)

translation :: FilePath -> FilePath -> Bool -> IO (Program, [ProgramType])
translation = hskToG2

prepBase :: FilePath -> IO ()
prepBase destination = do
    putStrLn $ "Downloading base to " ++ destination
    downloadBase destination
    putStrLn $ "Unpacking " ++ destination
    unpackTarSameDir destination

