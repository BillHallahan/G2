module G2.Internals.Language.Monad.TypeClasses (lookupTCDictTC) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeClasses
import G2.Internals.Language.Monad.Support

lookupTCDictTC :: FullState s m => Name -> Type -> m (Maybe Id)
lookupTCDictTC n t = do
    tc <- typeClasses
    return $ lookupTCDict tc n t