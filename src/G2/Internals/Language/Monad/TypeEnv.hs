module G2.Internals.Language.Monad.TypeEnv ( lookupT
                                           , insertT ) where

import G2.Internals.Language

import G2.Internals.Language.Monad.Support

import qualified Data.Map as M

import Prelude hiding( filter
                     , lookup
                     , map
                     , null)

liftTE :: ExState s m => (TypeEnv -> a) -> m a
liftTE f = return . f =<< typeEnv

lookupT :: ExState s m => Name -> m (Maybe AlgDataTy)
lookupT n = liftTE (M.lookup n)

insertT :: ExState s m => Name -> AlgDataTy -> m ()
insertT n t = do
    tenv <- typeEnv
    let tenv' = M.insert n t tenv
    putTypeEnv tenv'