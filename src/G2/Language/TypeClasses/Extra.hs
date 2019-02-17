module G2.Language.TypeClasses.Extra ( eqTCDict
                                     , numTCDict
                                     , ordTCDict
                                     , integralTCDict
                                     , structEqTCDict
                                     , lookupStructEqDicts
                                     , concreteSatEq
                                     , concreteSatStructEq
                                     , concreteSatTC ) where

import G2.Language.KnownValues
import G2.Language.Syntax
import G2.Language.TypeClasses.TypeClasses
import G2.Language.Typing

import Data.List
import Data.Maybe

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

lookupStructEqDicts :: KnownValues -> TypeClasses -> Maybe [(Type, Id)]
lookupStructEqDicts kv = lookupTCDicts (structEqTC kv)

concreteSatEq :: KnownValues -> TypeClasses -> Type -> Maybe Expr
concreteSatEq kv tc t = concreteSatTC tc (eqTC kv) t

concreteSatStructEq :: KnownValues -> TypeClasses -> Type -> Maybe Expr
concreteSatStructEq kv tc t = concreteSatTC tc (structEqTC kv) t

concreteSatTC :: TypeClasses -> Name -> Type -> Maybe Expr
concreteSatTC tc tcn t
    | TyCon _ _ <- tyAppCenter t
    , ts <- tyAppArgs t
    , tcs <- map (concreteSatTC tc tcn) ts
    , all (isJust) tcs =
    case lookupTCDict tc tcn t of
        Just i -> Just (foldl' App (Var i) $ map Type ts ++ map fromJust tcs)
        Nothing -> Nothing
concreteSatTC tc tcn t = fmap Var (lookupTCDict tc tcn t)
