module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language.Support
import G2.Internals.Preprocessing.NameCleaner
import G2.Internals.Preprocessing.WrapInteger

runPreprocessing :: State -> State
runPreprocessing = cleanNames . wrapInteger