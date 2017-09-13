module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language.Support
import G2.Internals.Preprocessing.Defunctionalizor
import G2.Internals.Preprocessing.FreeBind
import G2.Internals.Preprocessing.LetFloating
import G2.Internals.Preprocessing.NameCleaner

runPreprocessing :: State -> State
runPreprocessing = defunctionalize
				 . letFloat
				 . freeVarsBind
                 . cleanNames


