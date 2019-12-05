{-# LANGUAGE DeriveDataTypeable #-}

-- We define a datatype to hol the names of other data types we know should
-- exist, and that we care about for some special reason
-- (for example: the Bool type)
-- Try to avoid imports from G2 other than G2.Internal.Language.Syntax here!
module G2.Language.KnownValues where

import G2.Language.Syntax
import Data.Data (Data, Typeable)

data KnownValues = KnownValues {
                   tyInt :: Name
                 , dcInt :: Name

                 , tyFloat :: Name
                 , dcFloat :: Name

                 , tyDouble :: Name
                 , dcDouble :: Name

                 , tyInteger :: Name
                 , dcInteger :: Name

                 , tyChar :: Name
                 , dcChar :: Name

                 , tyBool :: Name
                 , dcTrue :: Name
                 , dcFalse :: Name

                 , tyList :: Name
                 , dcCons :: Name
                 , dcEmpty :: Name

                 , tyMaybe :: Name
                 , dcJust :: Name
                 , dcNothing :: Name

                 -- Typeclasses
                 , eqTC :: Name
                 , numTC :: Name
                 , ordTC :: Name
                 , integralTC :: Name
                 , realTC :: Name
                 , fractionalTC :: Name

                 -- Typeclass superclass extractors
                 , integralExtactReal :: Name
                 , realExtractNum :: Name
                 , realExtractOrd :: Name
                 , ordExtractEq :: Name

                 , eqFunc :: Name
                 , neqFunc :: Name

                 , plusFunc :: Name
                 , minusFunc :: Name
                 , timesFunc :: Name
                 , divFunc :: Name
                 , negateFunc :: Name
                 , modFunc :: Name

                 , fromIntegerFunc :: Name
                 , toIntegerFunc :: Name

                 , toRatioFunc :: Name
                 , fromRationalFunc :: Name

                 , geFunc :: Name
                 , gtFunc :: Name
                 , ltFunc :: Name
                 , leFunc :: Name

                 , structEqTC :: Name
                 , structEqFunc :: Name

                 , andFunc :: Name
                 , orFunc :: Name
                 , notFunc :: Name

                 , patErrorFunc :: Name
                 } deriving (Show, Eq, Read, Typeable, Data)
