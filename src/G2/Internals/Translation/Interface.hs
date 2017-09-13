module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace
import G2.Internals.Translation.PrimInject

translation :: FilePath -> FilePath -> FilePath -> IO (Program, [ProgramType])
translation proj src prims = do
    (data_prog, prog_tys) <- hskToG2 proj src
    prims <- mkPrims prims
    print prims
    let prim_prog = mergeProgs data_prog prims
    return . primInject $ dataInject prim_prog prog_tys
