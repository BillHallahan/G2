{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TyVarEnv (TyVarEnv
                            , empty
                            , insertTyVarEnv 
                            , lookupTyVarEnv 
                            , deleteTyVarEnv
                            , fromListTyVarEnv
                            , toListTyVarEnv ) where 

import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import G2.Language.Syntax

newtype TyVarEnv = TyVarEnv (HM.HashMap Name Type) deriving (Show, Eq, Read, Generic, Typeable, Data)

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insertTyVarEnv :: Name -> Type -> TyVarEnv -> TyVarEnv
insertTyVarEnv n ty (TyVarEnv env) = TyVarEnv $ HM.insert n ty env

lookupTyVarEnv :: Name -> TyVarEnv -> Maybe Type
lookupTyVarEnv n (TyVarEnv env) = HM.lookup n env

deleteTyVarEnv :: Name -> TyVarEnv -> TyVarEnv
deleteTyVarEnv n (TyVarEnv env) = TyVarEnv (HM.delete n env)

fromListTyVarEnv :: [(Name, Type)] -> TyVarEnv
fromListTyVarEnv = TyVarEnv . HM.fromList

toListTyVarEnv :: TyVarEnv -> [(Name, Type)]
toListTyVarEnv (TyVarEnv env) = HM.toList env

instance Hashable TyVarEnv

