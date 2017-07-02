module G2.Internals.Preprocessing.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing.Defunctionalizor
import G2.Internals.Preprocessing.PrimReplace

runPreprocessing :: State -> State
runPreprocessing = defunctionalize . primReplace