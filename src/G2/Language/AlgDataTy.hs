{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.AlgDataTy ( AlgDataTy (..)
                             , ADTSource (..)
                             , dataCon
                             , dataConWithName) where

import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable
import Data.List

import G2.Language.Syntax

data ADTSource = ADTSourceCode | ADTG2Generated deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable ADTSource

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = 
                 -- | A type defined using the `data` keyword.
                 DataTyCon { bound_ids :: [Id] -- ^ Polymorphic type variables
                           , data_cons :: [DataCon] -- ^ Data constructors for the type
                           , adt_source :: ADTSource
                           }
                 -- | A type defined using the `newtype` keyword.
               | NewTyCon { bound_ids :: [Id] -- ^ Polymorphic type variables
                          , data_con :: DataCon -- ^ The data constructor for the newtype
                          , rep_type :: Type -- ^ The type being wrapped by the newtype
                          , adt_source :: ADTSource
                          }
                 -- | A type defined using the `type` keyword.
               | TypeSynonym { bound_ids :: [Id]  -- ^ Polymorphic type variables
                             , synonym_of :: Type -- ^ What type is the type synonym equivalent to?
                             , adt_source :: ADTSource} deriving (Show, Eq, Read, Generic, Typeable, Data)

-- | Get the data constructors for the passed data type.
--
-- Warning: Does not "dig in" to type synonyms- a type synonym
-- will just give back an empty list.
dataCon :: AlgDataTy -> [DataCon]
dataCon (DataTyCon {data_cons = dc}) = dc
dataCon (NewTyCon {data_con = dc}) = [dc]
dataCon (TypeSynonym {}) = []

dataConWithName :: AlgDataTy -> Name -> Maybe DataCon
dataConWithName (DataTyCon _ dcs _) n = find (`dataConHasName` n) dcs
dataConWithName _ _ = Nothing

dataConHasName :: DataCon -> Name -> Bool
dataConHasName (DataCon n _ _ _) n' = n == n'

instance Hashable AlgDataTy