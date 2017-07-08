module G2.Internals.Preprocessing.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing.Defunctionalizor

runPreprocessing :: State -> State
runPreprocessing = defunctionalize