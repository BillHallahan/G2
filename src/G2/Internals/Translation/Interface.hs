module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace

translation :: FilePath -> FilePath -> IO (Program, [ProgramType])
translation m p = return . primReplace =<< hskToG2 m p