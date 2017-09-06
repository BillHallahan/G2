module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace
import G2.Internals.Translation.PrimInject

translation :: FilePath -> FilePath -> FilePath -> IO (Program, [ProgramType])
translation proj src prims = do
    raw_core <- hskToG2 proj src
    let data_core = (uncurry dataInject) raw_core
    prims <- mkPrims prims
    return data_core

