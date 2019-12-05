{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.TypeClasses.TypeClasses ( TypeClasses
                                           , Class (..)
                                           , initTypeClasses
                                           , insertClass
                                           , unionTypeClasses
                                           , isTypeClassNamed
                                           , isTypeClass
                                           , lookupTCDict
                                           , lookupTCDicts
                                           , lookupTCClass
                                           , tcWithNameMap
                                           , tcDicts
                                           , typeClassInst
                                           , satisfyingTCTypes
                                           , satisfyingTC
                                           , toMap) where

import G2.Language.AST
import G2.Language.KnownValues (KnownValues)
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing

import Data.Coerce
import Data.Data (Data, Typeable)
import Data.List
import qualified Data.Map as M
import Data.Maybe

data Class = Class { insts :: [(Type, Id)], typ_ids :: [Id], superclasses :: [(Type, Id)]}
                deriving (Show, Eq, Read, Typeable, Data)

type TCType = M.Map Name Class
newtype TypeClasses = TypeClasses TCType
                      deriving (Show, Eq, Read, Typeable, Data)

initTypeClasses :: [(Name, Id, [Id], [(Type, Id)])] -> TypeClasses
initTypeClasses nsi =
    let
        ns = map (\(n, _, i, sc) -> (n, i, sc)) nsi
        nsi' = filter (not . null . insts . snd)
             $ map (\(n, i, sc) -> 
                (n, Class { insts = mapMaybe (nameIdToTypeId n) nsi
                          , typ_ids = i
                          , superclasses = sc } )) ns
    in
    coerce $ M.fromList nsi'

insertClass :: Name -> Class -> TypeClasses -> TypeClasses
insertClass n c (TypeClasses tc) = TypeClasses (M.insert n c tc)

unionTypeClasses :: TypeClasses -> TypeClasses -> TypeClasses
unionTypeClasses (TypeClasses tc) (TypeClasses tc') = TypeClasses (M.union tc tc')

nameIdToTypeId :: Name -> (Name, Id, [Id], [(Type, Id)]) -> Maybe (Type, Id)
nameIdToTypeId nm (n, i, _, _) =
    let
        t = affectedType $ returnType i
    in
    if n == nm then fmap (, i) t else Nothing

affectedType :: Type -> Maybe Type
affectedType (TyApp (TyCon _ _) t) = Just t
affectedType _ = Nothing

isTypeClassNamed :: Name -> TypeClasses -> Bool
isTypeClassNamed n = M.member n . (coerce :: TypeClasses -> TCType)

isTypeClass :: TypeClasses -> Type -> Bool
isTypeClass tc (TyCon n _) = isTypeClassNamed n tc 
isTypeClass tc (TyApp t _) = isTypeClass tc t
isTypeClass _ _ = False

-- Returns the dictionary for the given typeclass and Type,
-- if one exists
lookupTCDict :: TypeClasses -> Name -> Type -> Maybe Id
lookupTCDict tc n t =
    case fmap insts $ M.lookup n (toMap tc) of
        Just c -> fmap snd $ find (\(t', _) -> PresType t .:: t') c
        Nothing -> Nothing

lookupTCDicts :: Name -> TypeClasses -> Maybe [(Type, Id)]
lookupTCDicts n = fmap insts . M.lookup n . coerce

lookupTCDictsTypes :: TypeClasses -> Name -> Maybe [Type]
lookupTCDictsTypes tc = fmap (map fst) . flip lookupTCDicts tc

lookupTCClass :: Name -> TypeClasses -> Maybe Class
lookupTCClass n = M.lookup n . coerce

tcWithNameMap :: Name -> [Id] -> M.Map Name Id
tcWithNameMap n =
    M.fromList
        . map (\i -> (forType $ typeOf i, i))
        . filter (isTC . typeOf)
    where
        forType :: Type -> Name
        forType (TyApp _ (TyVar (Id n' _))) = n'
        forType _ = error "Bad type in forType"

        isTC :: Type -> Bool
        isTC t = case tyAppCenter t of
                        TyCon n' _ -> n == n'
                        _ -> False

-- tcDicts
tcDicts :: TypeClasses -> [Id]
tcDicts = map snd . concatMap insts . M.elems . coerce

tyConAppName :: Type -> Maybe Name
tyConAppName (TyCon n _) = Just n
tyConAppName _ = Nothing

-- Given a TypeClass name, a type that you want an instance of that typeclass
-- for, and a mapping of TyVar name's to Id's for those types instances of
-- the typeclass, returns an instance of the typeclass, if possible 
typeClassInst :: TypeClasses -> M.Map Name Id -> Name -> Type -> Maybe Expr 
typeClassInst tc m tcn t
    | tca@(TyCon _ _) <- tyAppCenter t
    , ts <- tyAppArgs t
    , tcs <- map (typeClassInst tc m tcn) ts
    , all (isJust) tcs =
        case lookupTCDict tc tcn tca of
            Just i -> Just (foldl' App (Var i) $ map Type ts ++ map fromJust tcs)
            Nothing -> Nothing
    | (TyVar (Id n _)) <- tyAppCenter t
    , ts <- tyAppArgs t
    , tcs <- map (typeClassInst tc m tcn) ts
    , all (isJust) tcs =
        case M.lookup n m of
            Just i -> Just (foldl' App (Var i) $ map Type ts ++ map fromJust tcs)
            Nothing -> Nothing
typeClassInst _ _ _ _ = Nothing

-- satisfyingTCTypes
-- Finds types/dict pairs that satisfy the given TC requirements for the given polymorphic argument
-- returns a list of acceptable types
satisfyingTCTypes :: KnownValues -> TypeClasses -> Id -> [Type] -> [Type]
satisfyingTCTypes kv tc i ts =
    let
        tcReq = satisfyTCReq tc i ts
    in
    substKind i . inter kv $ mapMaybe (lookupTCDictsTypes tc) tcReq

inter :: KnownValues -> [[Type]] -> [Type]
inter kv [] = [tyInt kv]
inter _ xs = foldr1 intersect xs

substKind :: Id -> [Type] -> [Type]
substKind (Id _ t) ts = map (\t' -> case t' of 
                                        TyCon n _ -> TyCon n (tyFunToTyApp t)
                                        t'' -> t'') ts

tyFunToTyApp :: Type -> Type
tyFunToTyApp (TyFun t1 (TyFun t2 t3)) = TyApp (TyApp (tyFunToTyApp t1) (tyFunToTyApp t2)) (tyFunToTyApp t3)
tyFunToTyApp t = modifyChildren tyFunToTyApp t

-- satisfyingTCReq
-- Finds the names of the required typeclasses for a TyVar Id
-- See satisfyingTCTypes
satisfyTCReq :: TypeClasses -> Id -> [Type] -> [Name]
satisfyTCReq tc i =
    mapMaybe (tyConAppName . tyAppCenter) . filter (isFor i) . filter (isTypeClass tc)
    where
      isFor :: Id -> Type -> Bool
      isFor ii (TyApp (TyCon _ _) a) = ii `elem` tyVarIds a
      isFor _ _ = False

-- Given a list of type arguments and a mapping of TyVar Ids to actual Types
-- Gives the required TC's to pass to any TC arguments
satisfyingTC :: TypeClasses -> [Type] -> Id -> Type -> [Expr]
satisfyingTC  tc ts i t =
    let
        tcReq = satisfyTCReq tc i ts
    in
    map (\n -> case lookupTCDict tc n t of
                    Just i' -> Var i'
                    Nothing -> error "No typeclass found.") tcReq

toMap :: TypeClasses -> M.Map Name Class
toMap = coerce

instance ASTContainer TypeClasses Expr where
    containedASTs _ = []
    modifyContainedASTs _ = id

instance ASTContainer TypeClasses Type where
    containedASTs = containedASTs . (coerce :: TypeClasses -> TCType)
    modifyContainedASTs f = 
        coerce . modifyContainedASTs f . (coerce :: TypeClasses -> TCType)

instance ASTContainer Class Expr where
    containedASTs _ = []
    modifyContainedASTs _ = id

instance ASTContainer Class Type where
    containedASTs c = (containedASTs . insts $ c) ++ containedASTs (superclasses c)
    modifyContainedASTs f c = Class { insts = modifyContainedASTs f $ insts c
                                    , typ_ids = modifyContainedASTs f $ typ_ids c
                                    , superclasses = modifyContainedASTs f $ superclasses c}

instance Named TypeClasses where
    names = names . (coerce :: TypeClasses -> TCType)
    rename old new (TypeClasses m) =
        coerce $ M.mapKeys (rename old new) $ rename old new m
    renames hm (TypeClasses m) =
        coerce $ M.mapKeys (renames hm) $ renames hm m

instance Named Class where
    names = names . insts
    rename old new c = Class { insts = rename old new $ insts c
                             , typ_ids = rename old new $ typ_ids c
                             , superclasses = rename old new $ superclasses c }
    renames hm c = Class { insts = renames hm $ insts c
                         , typ_ids = renames hm $ typ_ids c
                         , superclasses = renames hm $ superclasses c }
