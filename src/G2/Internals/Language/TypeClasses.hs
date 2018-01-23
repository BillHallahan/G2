{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Language.TypeClasses ( TypeClasses (..)
                                         , initTypeClasses
                                         , isTypeClassNamed
                                         , eqTCDict
                                         , numTCDict
                                         , ordTCDict
                                         , lookupTCDict) where

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