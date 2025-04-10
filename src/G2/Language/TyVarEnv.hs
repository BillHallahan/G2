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
                            , toList 
                            , tyVarEnvCons
                            , toMap) where 

import Prelude hiding(lookup)
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Language.Syntax

newtype TyVarEnv = TyVarEnv (HM.HashMap Name Type) deriving (Show, Eq, Read, Generic, Typeable, Data)

tyVarEnvCons :: TyVarEnv -> HM.HashMap Name Type
tyVarEnvCons (TyVarEnv tyvarenv) = tyvarenv

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

toMap :: TyVarEnv -> M.Map Name Type 
toMap tvenv = M.fromList $ toList tvenv  

instance Hashable TyVarEnv

