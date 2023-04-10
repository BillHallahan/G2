{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

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
                              , qqDataConLookup

                              , toTHType ) where

import G2.Language as G2

import Language.Haskell.TH as TH

import GHC.Generics (Generic)
import Data.Data
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

data QQName = QQName T.Text (Maybe T.Text)
            deriving (Eq, Show, Read, Generic, Typeable, Data)

instance Hashable QQName

type QQMap = HM.HashMap QQName G2.Name

qqMap :: Named n => CleanedNames -> n -> QQMap
qqMap cn n =
    let
        ns = toList $ names n
    in
    HM.fromList $ zip (map (nameToQQName . renames cn) ns) ns

nameToQQName :: G2.Name -> QQName
nameToQQName (Name n m _ _) = QQName n m

thNameToQQName :: TH.Name -> QQName
thNameToQQName n =
    QQName (T.pack $ TH.nameBase n) (fmap T.pack $ TH.nameModule n)

-- | Maps a `QQName` to a `Name` with unique 0
qqNameToName0 :: QQName -> G2.Name
qqNameToName0 (QQName n m) = Name n m 0 Nothing

qqAlgDataTyLookup :: QQName -> QQMap -> TypeEnv -> Maybe AlgDataTy
qqAlgDataTyLookup qqn qqm tenv = flip HM.lookup tenv =<< HM.lookup qqn qqm

qqDataConLookup :: QQName -> QQName -> QQMap -> QQMap -> TypeEnv -> Maybe DataCon
qqDataConLookup qqtn qqdcn type_nm_qqm dc_nm_qqm tenv
    | Just adt <- qqAlgDataTyLookup qqtn type_nm_qqm tenv
    , Just dcn <- HM.lookup qqdcn dc_nm_qqm = dataConWithName adt dcn
    | otherwise = Nothing

toTHType :: CleanedNames -> G2.Type -> Q TH.Type
toTHType cleaned (TyFun t1 t2) = appT (appT arrowT $ toTHType cleaned t1) (toTHType cleaned t2)
toTHType cleaned (TyApp t1 t2) = appT (toTHType cleaned t1) (toTHType cleaned t2)
toTHType cleaned t@(TyCon n _)
    | nameOcc (renames cleaned n) == "List" = listT -- GHC 9.6 on
    | nameOcc (renames cleaned n) == "[]" = listT -- pre GHC 9.6
    | Just i <- tupleNum . nameOcc $ renames cleaned n = tupleT i
    | otherwise = do
        tn <- lookupTypeName . T.unpack . nameOcc $ renames cleaned n
        case tn of
            Just tn' -> conT tn'
            Nothing -> error $ "toTHType: Unhandled case\n" ++ show (renames cleaned t)
toTHType _ t = error $ "toTHType: Unhandled case\n" ++ show t

tupleNum :: T.Text -> Maybe Int
tupleNum = tupleNum' 0 . T.unpack

tupleNum' :: Int -> String -> Maybe Int
tupleNum' 0 ("()") = Just 0
tupleNum' 0 ('(':xs) = tupleNum' 1 xs
tupleNum' !n (',':xs) = tupleNum' (1 + n) xs
tupleNum' !n ")" = Just n
tupleNum' _ _ = Nothing