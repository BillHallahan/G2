{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TyVarEnv (TyVarEnv
                            , empty
                            , insert
                            , insertSymbolic
                            , lookup
                            , delete
                            , fromList 
                            , toList 
                            , tyVarEnvCons
                            , toMap
                            , deepLookup
                            , deepLookupName) where 

import Prelude hiding(lookup)
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import G2.Language.Syntax

data TyConcOrSym = TyConc Type
                 | TySym Id
                 deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable TyConcOrSym

tyConcOrSymToType :: TyConcOrSym -> Type
tyConcOrSymToType (TyConc t) = t
tyConcOrSymToType (TySym i) = TyVar i

newtype TyVarEnv = TyVarEnv (HM.HashMap Name TyConcOrSym) deriving (Show, Eq, Read, Generic, Typeable, Data)

-- ToDo: is this function necessary?
tyVarEnvCons :: TyVarEnv -> HM.HashMap Name Type
tyVarEnvCons (TyVarEnv tyvarenv) = HM.map tyConcOrSymToType tyvarenv

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insert :: Name -> Type -> TyVarEnv -> TyVarEnv
insert n ty (TyVarEnv env) = TyVarEnv $ HM.insert n (TyConc ty) env

insertSymbolic :: Id -> TyVarEnv -> TyVarEnv
insertSymbolic ty (TyVarEnv env) = TyVarEnv $ HM.insert (idName ty) (TySym ty) env

lookup :: Name -> TyVarEnv -> Maybe Type
lookup n (TyVarEnv env) = tyConcOrSymToType <$> HM.lookup n env

-- a recursive version of lookup that aim to find the concrete types of type variable
deepLookup :: TyVarEnv -> Expr -> Maybe Type
deepLookup tv (Type (TyVar (Id n _))) = deepLookupName tv n
deepLookup _ (Type t) = Just t
deepLookup tv (Var (Id n _)) = deepLookupName tv n 
deepLookup _ _  = Nothing 

deepLookupName :: TyVarEnv -> Name -> Maybe Type
deepLookupName tv_env n = case lookup n tv_env of
    Just (TyVar (Id n' _)) -> deepLookupName tv_env n'
    Just t -> Just t 
    Nothing -> Nothing

delete :: Name -> TyVarEnv -> TyVarEnv
delete n (TyVarEnv env) = TyVarEnv (HM.delete n env)

fromList :: [(Name, Type)] -> TyVarEnv
fromList = TyVarEnv . HM.map TyConc . HM.fromList

toList :: TyVarEnv -> [(Name, Type)]
toList = HM.toList . tyVarEnvCons

toMap :: TyVarEnv -> M.Map Name Type 
toMap tvenv = M.fromList $ toList tvenv  

instance Hashable TyVarEnv