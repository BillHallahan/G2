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
                            , union
                            , fromList
                            , toList
                            , toListConcOrSym
                            , fromListConcOrSym
                            , toUFMap
                            , toTypeUFMap
                            , deepLookup
                            , deepLookupName) where 

import Prelude hiding(lookup)
import GHC.Generics (Generic)
import Control.Exception
import Data.Bifunctor
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import G2.Language.Syntax
import qualified G2.Data.UFMap as UF

-- The TyVarEnv is really just a wrapper on a `UF.UFMap Name TyConcOrSym`.
-- We maintain an invariant that a TyVar is never wrapped inside a TyConc.
-- Instead, TyVar's always mapped to TySym's, or directly to the Type that they are instantiated with.
-- When a TyVar is mapped to another TyVar, we union those TyVar Names in the UFMap.
-- This ensures we do not inconsistently concretize two TyVars that have been unioned.

data TyConcOrSym = TyConc Type
                 | TySym Id
                 deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable TyConcOrSym

tyConcOrSymToType :: TyConcOrSym -> Type
tyConcOrSymToType (TyConc t) = t
tyConcOrSymToType (TySym i) = TyVar i

newtype TyVarEnv = TyVarEnv (UF.UFMap Name TyConcOrSym) deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable TyVarEnv

tyVarEnvCons :: TyVarEnv -> HM.HashMap Name Type
tyVarEnvCons (TyVarEnv env) = HM.map tyConcOrSymToType $ UF.toSimpleMap env

empty :: TyVarEnv
empty = TyVarEnv UF.empty

insert :: Name -> Type -> TyVarEnv -> TyVarEnv
insert n (TyVar i@(Id n' _)) (TyVarEnv env)
    | UF.member n env || UF.member n' env = TyVarEnv $ UF.join const n n' env
    | otherwise = TyVarEnv . UF.join const n n' $ UF.insert (idName i) (TySym i) env
insert n ty (TyVarEnv env) = TyVarEnv $ UF.insert n (TyConc ty) env

insertSymbolic :: Id -> TyVarEnv -> TyVarEnv
insertSymbolic ty (TyVarEnv env) = TyVarEnv $ UF.insert (idName ty) (TySym ty) env

isSymbolic :: Name -> TyVarEnv -> Bool
isSymbolic n tv_env | Just (TySym _) <- lookupConcOrSym n tv_env = True
                    | otherwise = False

lookup :: Name -> TyVarEnv -> Maybe Type
lookup n (TyVarEnv env) = tyConcOrSymToType <$> UF.lookup n env

lookupConcOrSym :: Name -> TyVarEnv -> Maybe TyConcOrSym
lookupConcOrSym n (TyVarEnv env) = UF.lookup n env

member :: Name -> TyVarEnv -> Bool
member n (TyVarEnv env) = UF.member n env

union :: TyVarEnv -> TyVarEnv -> TyVarEnv
union (TyVarEnv env1) (TyVarEnv env2) = TyVarEnv $ UF.unionWith favorConc env1 env2
    where
        favorConc t@(TyConc _) _ = t
        favorConc _ t = t

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
deepLookupNameConcOrSym tv_env@(TyVarEnv tv) n = case UF.lookup n tv of
    Just t@(TySym _) -> Just t
    Just (TyConc (TyVar (Id ty_n _))) -> deepLookupNameConcOrSym tv_env ty_n
    Just t@(TyConc _) -> Just t
    Nothing -> Nothing

fromList :: [(Name, Type)] -> TyVarEnv
fromList = foldr (uncurry insert) empty

toList :: TyVarEnv -> [(Name, Type)]
toList = HM.toList . tyVarEnvCons

toListConcOrSym :: TyVarEnv -> [([Name], TyConcOrSym)]
toListConcOrSym (TyVarEnv tv_env) =
    let lst = UF.toList tv_env in
    assert (all (isJust . snd) lst) $ map (second fromJust) lst

fromListConcOrSym :: [([Name], TyConcOrSym)] -> TyVarEnv 
fromListConcOrSym = TyVarEnv . UF.fromList . map (second Just)

toUFMap :: TyVarEnv -> UF.UFMap Name TyConcOrSym
toUFMap (TyVarEnv env) = env

toTypeUFMap :: TyVarEnv -> UF.UFMap Name Type
toTypeUFMap (TyVarEnv env) = UF.map tyConcOrSymToType env