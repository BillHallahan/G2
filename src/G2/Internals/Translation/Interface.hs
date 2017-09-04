module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace
import G2.Internals.Translation.PrimInject

translation :: FilePath -> FilePath -> IO (Program, [ProgramType])
translation m p = return . primInject =<< hskToG2 m p