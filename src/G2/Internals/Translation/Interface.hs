module G2.Internals.Translation.Interface where

import G2.Internals.Language.Syntax
import G2.Internals.Translation.Haskell
import G2.Internals.Translation.PrimReplace
import G2.Internals.Translation.PrimInject

translation :: FilePath -> FilePath -> IO (Program, [ProgramType])
-- translation m p = return . primReplace =<< hskToG2 m p
translation src proj = do
    (prog, ptypes) <- hskToG2 src proj
    let prog' = primInject prog
    return (prog', ptypes)

