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
                            , toMap
                            , deepLookup
                            , deepLookup') where 

import Prelude hiding(lookup)
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Language.Syntax

newtype TyVarEnv = TyVarEnv (HM.HashMap Name Type) deriving (Show, Eq, Read, Generic, Typeable, Data)

-- ToDo: is this function necessary?
tyVarEnvCons :: TyVarEnv -> HM.HashMap Name Type
tyVarEnvCons (TyVarEnv tyvarenv) = tyvarenv

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insert :: Name -> Type -> TyVarEnv -> TyVarEnv
insert n ty (TyVarEnv env) = TyVarEnv $ HM.insert n ty env

lookup :: Name -> TyVarEnv -> Maybe Type
lookup n (TyVarEnv env) = HM.lookup n env

-- a recursive version of lookup that aim to find the concrete types of type variable
deepLookup :: TyVarEnv -> Expr -> Maybe Type
deepLookup _ (Type t) = Just t
deepLookup tv (Var (Id n _)) = deepLookup' tv n 
deepLookup _ _  = Nothing 

deepLookup' :: TyVarEnv -> Name -> Maybe Type
deepLookup' tv@(TyVarEnv env) n = case HM.lookup n env of
    Just (TyVar (Id n' _)) -> deepLookup' tv n'
    Just t -> Just t 
    Nothing -> Nothing

delete :: Name -> TyVarEnv -> TyVarEnv
delete n (TyVarEnv env) = TyVarEnv (HM.delete n env)

fromList :: [(Name, Type)] -> TyVarEnv
fromList = TyVarEnv . HM.fromList

toList :: TyVarEnv -> [(Name, Type)]
toList (TyVarEnv env) = HM.toList env

toMap :: TyVarEnv -> M.Map Name Type 
toMap tvenv = M.fromList $ toList tvenv  

instance Hashable TyVarEnv