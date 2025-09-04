{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, FlexibleInstances, MultiParamTypeClasses #-}

module G2.Language.TyVarEnv ( TyVarEnv
                            , TyConcOrSym (..)
                            , empty
                            , insert
                            , insertSymbolic
                            , isSymbolic
                            , lookup
                            , lookupConcOrSym
                            , member
                            , delete
                            , fromList 
                            , toList
                            , toListConcOrSym
                            , fromListConcOrSym
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

instance Hashable TyVarEnv

tyVarEnvCons :: TyVarEnv -> HM.HashMap Name Type
tyVarEnvCons (TyVarEnv tyvarenv) = HM.map tyConcOrSymToType tyvarenv

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insert :: Name -> Type -> TyVarEnv -> TyVarEnv
insert n ty (TyVarEnv env) = TyVarEnv $ HM.insert n (TyConc ty) env

insertSymbolic :: Id -> TyVarEnv -> TyVarEnv
insertSymbolic ty (TyVarEnv env) = TyVarEnv $ HM.insert (idName ty) (TySym ty) env

isSymbolic :: Name -> TyVarEnv -> Bool
isSymbolic n tv_env | Just (TySym _) <- lookupConcOrSym n tv_env = True
                    | otherwise = False

lookup :: Name -> TyVarEnv -> Maybe Type
lookup n (TyVarEnv env) = tyConcOrSymToType <$> HM.lookup n env

lookupConcOrSym :: Name -> TyVarEnv -> Maybe TyConcOrSym
lookupConcOrSym n (TyVarEnv env) = HM.lookup n env

member :: Name -> TyVarEnv -> Bool
member n (TyVarEnv env) = HM.member n env

-- a recursive version of lookup that aim to find the concrete types of type variable
deepLookup :: TyVarEnv -> Expr -> Maybe Type
deepLookup tv (Type (TyVar (Id n _))) = deepLookupName tv n
deepLookup _ (Type t) = Just t
deepLookup tv (Var (Id n _)) = deepLookupName tv n 
deepLookup _ _  = Nothing 

deepLookupName :: TyVarEnv -> Name -> Maybe Type
deepLookupName tv_env n = case deepLookupNameConcOrSym tv_env n of
    Just (TySym i) -> Just (TyVar i)
    Just (TyConc t) -> Just t 
    Nothing -> Nothing

deepLookupNameConcOrSym :: TyVarEnv -> Name -> Maybe TyConcOrSym
deepLookupNameConcOrSym tv_env@(TyVarEnv tv) n = case HM.lookup n tv of
    Just t@(TySym _) -> Just t
    Just (TyConc (TyVar (Id ty_n _))) -> deepLookupNameConcOrSym tv_env ty_n
    Just t@(TyConc _) -> Just t
    Nothing -> Nothing

delete :: Name -> TyVarEnv -> TyVarEnv
delete n (TyVarEnv env) = TyVarEnv (HM.delete n env)

fromList :: [(Name, Type)] -> TyVarEnv
fromList = TyVarEnv . HM.map TyConc . HM.fromList

toList :: TyVarEnv -> [(Name, Type)]
toList = HM.toList . tyVarEnvCons

toListConcOrSym :: TyVarEnv -> [(Name, TyConcOrSym)]
toListConcOrSym (TyVarEnv tv_env) = HM.toList tv_env

fromListConcOrSym :: [(Name, TyConcOrSym)] -> TyVarEnv 
fromListConcOrSym = TyVarEnv . HM.fromList

toMap :: TyVarEnv -> M.Map Name Type 
toMap tvenv = M.fromList $ toList tvenv  