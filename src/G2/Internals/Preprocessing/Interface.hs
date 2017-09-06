module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language.Support
import G2.Internals.Preprocessing.Defunctionalizor
import G2.Internals.Preprocessing.NameCleaner

runPreprocessing :: State -> State
runPreprocessing = defunctionalize 
                 . cleanNames


