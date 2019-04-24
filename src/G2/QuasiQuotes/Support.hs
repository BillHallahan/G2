{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

-- Converts types with Name's to types with QQNames, since uniques in the
-- QuasiQuoter will most likely not match up with uniques from the original
-- code

module G2.QuasiQuotes.Support ( QQName (..)
                              , QQMap
                              , qqMap
                              , nameToQQName
                              , thNameToQQName
                              , qqNameToName0

                              , qqAlgDataTyLookup
                              , qqDataConLookup ) where

import G2.Language

import qualified Language.Haskell.TH as TH

import GHC.Generics (Generic)
import Data.Data
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map as M
import qualified Data.Text as T

import Debug.Trace

data QQName = QQName T.Text (Maybe T.Text)
            deriving (Eq, Show, Read, Generic, Typeable, Data)

instance Hashable QQName

type QQMap = HM.HashMap QQName Name

qqMap :: Named n => CleanedNames -> n -> QQMap
qqMap cn n =
    let
        ns = names n
    in
    HM.fromList $ zip (map (nameToQQName . renames cn) ns) ns

nameToQQName :: Name -> QQName
nameToQQName (Name n m _ _) = QQName n m

thNameToQQName :: TH.Name -> QQName
thNameToQQName n =
    QQName (T.pack $ TH.nameBase n) (fmap T.pack $ TH.nameModule n)

-- | Maps a `QQName` to a `Name` with unique 0
qqNameToName0 :: QQName -> Name
qqNameToName0 (QQName n m) = Name n m 0 Nothing

qqAlgDataTyLookup :: QQName -> QQMap -> TypeEnv -> Maybe AlgDataTy
qqAlgDataTyLookup qqn qqm tenv = flip M.lookup tenv =<< HM.lookup qqn qqm

qqDataConLookup :: QQName -> QQName -> QQMap -> TypeEnv -> Maybe DataCon
qqDataConLookup qqtn qqdcn qqm tenv
    | Just adt <- qqAlgDataTyLookup qqtn qqm tenv
    , Just dcn <- HM.lookup qqdcn qqm =
        trace ("qqDataConLookup adt = " ++ show adt ++ "\ndcn = " ++ show dcn ++ "\nres = " ++ show (dataConWithName adt dcn)) dataConWithName adt dcn
    | otherwise = Nothing