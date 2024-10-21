{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}


module G2.Language.KnownValues where

-- Try to avoid imports from G2 other than G2..Language.Syntax here!
import G2.Language.Syntax
import Data.Data (Data, Typeable)
import Data.Hashable
import GHC.Generics (Generic)

-- | A `KnownValues` tracks the names of  data types we know should
-- exist, and that we care about for some special reason.
data KnownValues = KnownValues {
                   tyCoercion :: Name
                 , dcCoercion :: Name 
                 
                 , tyInt :: Name
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

                 , tyRational :: Name

                 , tyList :: Name
                 , dcCons :: Name
                 , dcEmpty :: Name

                 , tyMaybe :: Name
                 , dcJust :: Name
                 , dcNothing :: Name

                 , tyUnit :: Name
                 , dcUnit :: Name

                 , tyMutVar :: Name
                 , dcMutVar :: Name

                 , tyState :: Name
                 , dcState :: Name

                 , tyRealWorld :: Name
                 , dcRealWorld :: Name

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

                 , impliesFunc :: Name
                 , iffFunc :: Name

                 , andFunc :: Name
                 , orFunc :: Name
                 , notFunc :: Name

                 , errorFunc :: Name
                 , errorWithoutStackTraceFunc :: Name
                 , errorEmptyListFunc :: Name
                 , patErrorFunc :: Name
                 } deriving (Show, Eq, Read, Typeable, Data, Generic)

instance Hashable KnownValues

-- | Checks if the `Name` corresponds to a function that is an error.
isErrorFunc :: KnownValues -> Name -> Bool
isErrorFunc kv n =    n == errorFunc kv
                   || n == errorEmptyListFunc kv    
                   || n == errorWithoutStackTraceFunc kv
                   || n == patErrorFunc kv
