{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeClasses ( TypeClasses (..)
                                         , Class (..)
                                         , initTypeClasses
                                         , isTypeClassNamed
                                         , isTypeClass
                                         , eqTCDict
                                         , numTCDict
                                         , ordTCDict
                                         , integralTCDict
                                         , structEqTCDict
                                         , lookupTCDict
                                         , lookupTCDicts
                                         , lookupEqDicts
                                         , lookupStructEqDicts
                                         , tcDicts
                                         , concreteSatEq
                                         , concreteSatStructEq
                                         , concreteSatTC
                                         , satisfyingTCTypes
                                         , satisfyingTC) where

import G2.Internals.Language.AST
import G2.Internals.Language.KnownValues
import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax
import G2.Internals.Language.Typing

import Data.Coerce
import Data.List
import qualified Data.Map as M
import Data.Maybe

data Class = Class { insts :: [(Type, Id)], typ_ids :: [Id]} deriving (Show, Eq, Read)

type TCType = M.Map Name Class
newtype TypeClasses = TypeClasses TCType
                      deriving (Show, Eq, Read)

initTypeClasses :: [(Name, Id, [Id])] -> TypeClasses
initTypeClasses nsi =
    let
        ns = map (\(n, _, i) -> (n, i)) nsi
        nsi' = filter (not . null . insts . snd)
             $ map (\(n, i) -> (n, Class { insts = mapMaybe (nameIdToTypeId n) nsi, typ_ids = i } )) ns
    in
    coerce $ M.fromList nsi'

nameIdToTypeId :: Name -> (Name, Id, [Id]) -> Maybe (Type, Id)
nameIdToTypeId nm (n, i, _) =
    let
        t = affectedType $ returnType i
    in
    if n == nm then fmap (, i) t else Nothing

affectedType :: Type -> Maybe Type
affectedType (TyConApp _ [t]) = Just t
affectedType _ = Nothing

isTypeClassNamed :: Name -> TypeClasses -> Bool
isTypeClassNamed n = M.member n . (coerce :: TypeClasses -> TCType)

isTypeClass :: TypeClasses -> Type -> Bool
isTypeClass tc (TyConApp n _) = isTypeClassNamed n tc 
isTypeClass _ _ = False

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
    containedASTs = containedASTs . insts
    modifyContainedASTs f c = Class { insts = modifyContainedASTs f $ insts c
                                    , typ_ids = modifyContainedASTs f $ typ_ids c}

instance Named TypeClasses where
    names = names . (coerce :: TypeClasses -> TCType)
    rename old new (TypeClasses m) =
        coerce $ M.mapKeys (rename old new) $ rename old new m
    renames hm (TypeClasses m) =
        coerce $ M.mapKeys (renames hm) $ renames hm m

instance Named Class where
    names = names . insts
    rename old new c = Class { insts = rename old new $ insts c
                             , typ_ids = rename old new $ typ_ids c }
    renames hm c = Class { insts = renames hm $ insts c
                         , typ_ids = renames hm $ typ_ids c }

eqTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
eqTCDict kv tc t = lookupTCDict tc (eqTC kv) t

numTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
numTCDict kv tc t = lookupTCDict tc (numTC kv) t

ordTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
ordTCDict kv tc t = lookupTCDict tc (ordTC kv) t

integralTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
integralTCDict kv tc t = lookupTCDict tc (integralTC kv) t

structEqTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
structEqTCDict kv tc t = lookupTCDict tc (structEqTC kv) t


-- Returns the dictionary for the given typeclass and Type,
-- if one exists
lookupTCDict :: TypeClasses -> Name -> Type -> Maybe Id
lookupTCDict tc (Name n _ _ _) t =
    case (fmap (insts . snd) $ find (\(Name n' _ _ _, _) -> n == n') (M.toList ((coerce :: TypeClasses -> TCType) tc))) of
        Just c -> fmap snd $ find (\(t', _) -> t .:: t') c
        Nothing -> Nothing

lookupEqDicts :: KnownValues -> TypeClasses -> Maybe [(Type, Id)]
lookupEqDicts kv = lookupTCDicts (eqTC kv)

lookupStructEqDicts :: KnownValues -> TypeClasses -> Maybe [(Type, Id)]
lookupStructEqDicts kv = lookupTCDicts (structEqTC kv)

lookupTCDicts :: Name -> TypeClasses -> Maybe [(Type, Id)]
lookupTCDicts n = fmap insts . M.lookup n . coerce

lookupTCDictsTypes :: Name -> TypeClasses -> Maybe [Type]
lookupTCDictsTypes n = fmap (map fst) . lookupTCDicts n

-- tcDicts
tcDicts :: TypeClasses -> [Id]
tcDicts = map snd . concatMap insts . M.elems . coerce

-- satisfyingTCTypes
-- Finds all types/dict paurs that satisfy the given TC requirements for each polymorphic argument
-- returns a list of tuples, where each tuple (i, t) corresponds to a TyVar Id i,
-- and a list of acceptable types
satisfyingTCTypes :: TypeClasses -> [Type] -> [(Id, [Type])]
satisfyingTCTypes tc ts =
    let
        tcReq = satisfyTCReq tc ts

        tcReqTS = map (\(i, ns) -> (i, mapMaybe (flip lookupTCDictsTypes tc) ns)) tcReq
    in
    map (\(i, ts') -> (i, inter ts')) tcReqTS

-- satisfyingTCReq
-- Finds the names of the required typeclasses for each TyVar Id
-- See satisfyingTCTypes
satisfyTCReq :: TypeClasses -> [Type] -> [(Id, [Name])]
satisfyTCReq tc ts =
    map (\(i, ts') -> (i, mapMaybe tyConAppName ts'))
    $ mapMaybe toIdTypeTup
    $ groupBy (\t1 t2 -> tyConAppArg t1 == tyConAppArg t2)
    $ filter (typeClassReq tc) ts

toIdTypeTup :: [Type] -> Maybe (Id, [Type])
toIdTypeTup ts@(TyConApp _ [TyVar i]:_) = Just (i, ts)
toIdTypeTup _ = Nothing

typeClassReq :: TypeClasses -> Type -> Bool
typeClassReq tc (TyConApp n _) = isTypeClassNamed n tc
typeClassReq _ _ = False

tyConAppName :: Type -> Maybe Name
tyConAppName (TyConApp n _) = Just n
tyConAppName _ = Nothing

tyConAppArg :: Type -> [Type]
tyConAppArg (TyConApp _ ts) = ts
tyConAppArg _ = []

inter :: Eq a => [[a]] -> [a]
inter [] = []
inter xs = foldr1 intersect xs

concreteSatEq :: KnownValues -> TypeClasses -> Type -> Expr
concreteSatEq kv tc t = concreteSatTC tc (eqTC kv) t

concreteSatStructEq :: KnownValues -> TypeClasses -> Type -> Expr
concreteSatStructEq kv tc t = concreteSatTC tc (structEqTC kv) t

concreteSatTC :: TypeClasses -> Name -> Type -> Expr
concreteSatTC tc tcn t@(TyConApp _ ts) =
    case lookupTCDict tc tcn t of
        Just i -> foldl' App (Var i) $ map Type ts ++  map (concreteSatTC tc tcn) ts
        Nothing -> error $ "Unknown typeclass in concreteSatTC"
concreteSatTC tc tcn t =
    case lookupTCDict tc tcn t of
        Just i -> Var i
        Nothing -> error "Unknown typeclass in concreteSatTC"

-- Given a list of type arguments and a mapping of TyVar Ids to actual Types
-- Gives the required TC's to pass to any TC arguments
satisfyingTC :: TypeClasses -> [Type] -> [(Id, Type)] -> [Id]
satisfyingTC  tc ts it =
    let
        tcReq = satisfyTCReq tc ts
    in
    concat
    $ mapMaybe 
        (\(i, t) -> fmap (mapMaybe (\n -> lookupTCDict tc n t))
                         (lookup i tcReq)
        ) it
