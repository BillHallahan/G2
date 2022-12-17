module G2.Language.Monad.TypeEnv ( lookupT
                                 , insertT ) where

import G2.Language

import G2.Language.Monad.Support

import qualified Data.HashMap.Lazy as HM

import Prelude hiding( filter
                     , lookup
                     , map
                     , null)

liftTE :: ExState s m => (TypeEnv -> a) -> m a
liftTE f = return . f =<< typeEnv

lookupT :: ExState s m => Name -> m (Maybe AlgDataTy)
lookupT n = liftTE (HM.lookup n)

insertT :: ExState s m => Name -> AlgDataTy -> m ()
insertT n t = do
    tenv <- typeEnv
    let tenv' = HM.insert n t tenv
    putTypeEnv tenv'
