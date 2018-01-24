{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeClasses ( TypeClasses (..)
                                         , initTypeClasses
                                         , isTypeClassNamed
                                         , isTypeClass
                                         , eqTCDict
                                         , numTCDict
                                         , ordTCDict
                                         , lookupTCDict
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

type TCType = M.Map Name [(Type, Id)]
newtype TypeClasses = TypeClasses TCType
                      deriving (Show, Eq, Read)

initTypeClasses :: [(Name, Id)] -> TypeClasses
initTypeClasses nsi =
    let
        ns = map fst nsi
        nsi' = filter (not . null . snd)
             $ map (\n -> (n, mapMaybe (nameIdToTypeId n) nsi)) ns
    in
    coerce $ M.fromList nsi'

nameIdToTypeId :: Name -> (Name, Id) -> Maybe (Type, Id)
nameIdToTypeId nm (n, i) =
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

instance Named TypeClasses where
    names = names . (coerce :: TypeClasses -> TCType)
    rename old new (TypeClasses m) =
        coerce $ M.mapKeys (rename old new) $ rename old new m

eqTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
eqTCDict kv tc t = lookupTCDict tc (eqTC kv) t

numTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
numTCDict kv tc t = lookupTCDict tc (numTC kv) t

ordTCDict :: KnownValues -> TypeClasses -> Type -> Maybe Id
ordTCDict kv tc t = lookupTCDict tc (ordTC kv) t

lookupTCDict2 :: TypeClasses -> Name -> Type -> Maybe (Name, [(Type, Id)])
lookupTCDict2 tc (Name n _ _) t =
    find (\(Name n' _ _, _) -> n == n') (M.toList ((coerce :: TypeClasses -> TCType) tc))

lookupTCDict3 :: TypeClasses -> Name -> Type -> Maybe [(Type, Id)]
lookupTCDict3 tc n t =  fmap snd $ lookupTCDict2 tc n t

-- Returns the dictionary for the given typeclass and Type,
-- if one exists
lookupTCDict :: TypeClasses -> Name -> Type -> Maybe Id
lookupTCDict tc (Name n _ _) t =
    (fmap snd $ find (\(Name n' _ _, _) -> n == n') (M.toList ((coerce :: TypeClasses -> TCType) tc))) -- M.lookup n ((coerce :: TypeClasses -> TCType) tc) 
    >>= fmap snd . find (\(t', _) -> t .:: t')

lookupTCDicts :: Name -> TypeClasses -> Maybe [(Type, Id)]
lookupTCDicts n = M.lookup n . coerce

lookupTCDictsTypes :: Name -> TypeClasses -> Maybe [Type]
lookupTCDictsTypes n = fmap (map fst) . lookupTCDicts n

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
    map (\(i, ts) -> (i, inter ts)) tcReqTS

-- satisfyingTCReq
-- Finds the names of the required typeclasses for each TyVar Id
-- See satisfyingTCTypes
satisfyTCReq :: TypeClasses -> [Type] -> [(Id, [Name])]
satisfyTCReq tc ts =
    filter (not . null . snd) 
    $ map (\(i, ts) -> (i, mapMaybe tyConAppName ts))
    $ mapMaybe toIdTypeTup
    $ groupBy (\t1 t2 -> tyConAppArg t1 == tyConAppArg t2)
    $ filter (typeClassReq tc) ts

toIdTypeTup :: [Type] -> Maybe (Id, [Type])
toIdTypeTup ts@(TyConApp nt [TyVar i]:_) = Just (i, ts)
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
