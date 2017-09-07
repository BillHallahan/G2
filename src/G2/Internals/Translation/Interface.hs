module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace
import G2.Internals.Translation.PrimInject

translation :: FilePath -> FilePath -> FilePath -> IO (Program, [ProgramType])
translation proj src prims = do
    raw_core <- hskToG2 proj src
    let (data_prog, prog_tys) = (uncurry dataInject) raw_core
    prims <- mkPrims prims
    let prim_prog = mergeProgs data_prog prims
    return . primInject $ dataInject prim_prog prog_tys
