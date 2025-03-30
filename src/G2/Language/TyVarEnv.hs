{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TyVarEnv (TyVarEnv
                            , empty
                            , insert
                            , lookup
                            , delete
                            , fromList 
                            , toList ) where 

import Prelude hiding(lookup)
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import G2.Language.Syntax

newtype TyVarEnv = TyVarEnv (HM.HashMap Name Type) deriving (Show, Eq, Read, Generic, Typeable, Data)

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insert :: Name -> Type -> TyVarEnv -> TyVarEnv
insert n ty (TyVarEnv env) = TyVarEnv $ HM.insert n ty env

lookup :: Name -> TyVarEnv -> Maybe Type
lookup n (TyVarEnv env) = HM.lookup n env

delete :: Name -> TyVarEnv -> TyVarEnv
delete n (TyVarEnv env) = TyVarEnv (HM.delete n env)

fromList :: [(Name, Type)] -> TyVarEnv
fromList = TyVarEnv . HM.fromList

toList :: TyVarEnv -> [(Name, Type)]
toList (TyVarEnv env) = HM.toList env

instance Hashable TyVarEnv

