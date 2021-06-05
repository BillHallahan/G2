{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Language.AlgDataTy where

import Data.Data (Data, Typeable)

import G2.Language.Syntax


type ProgramType = (Name, AlgDataTy)

-- | Algebraic data types are types constructed with parametrization of some
-- names over types, and a list of data constructors for said type.
data AlgDataTy = DataTyCon { bound_ids :: [Id]
                           , data_cons :: [DataCon] }
               | NewTyCon { bound_ids :: [Id]
                          , data_con :: DataCon
                          , rep_type :: Type }
               | TypeSynonym { bound_ids :: [Id]
                             , synonym_of :: Type
                             } deriving (Show, Eq, Read, Typeable, Data)


