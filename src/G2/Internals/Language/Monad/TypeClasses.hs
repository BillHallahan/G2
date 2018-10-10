module G2.Internals.Language.Monad.TypeClasses ( lookupTCDictTC
                                               , typeClassInstTC
                                               , numTCM
                                               , ordTCM ) where

import qualified G2.Internals.Language.KnownValues as KV
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeClasses
import G2.Internals.Language.Monad.Support

import qualified Data.Map as M

lookupTCDictTC :: FullState s m => Name -> Type -> m (Maybe Id)
lookupTCDictTC n t = do
    tc <- typeClasses
    return $ lookupTCDict tc n t

typeClassInstTC :: FullState s m => M.Map Name Id -> Name -> Type -> m (Maybe Expr)
typeClassInstTC m n t = do
    tc <- typeClasses
    return $ typeClassInst tc m n t

numTCM :: FullState s m => m Name
numTCM = return . KV.numTC =<< knownValues

ordTCM :: FullState s m => m Name
ordTCM = return . KV.ordTC =<< knownValues