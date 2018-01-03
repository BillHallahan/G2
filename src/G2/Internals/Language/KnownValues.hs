-- We define a datatype to hol the names of other data types we know should
-- exist, and that we care about for some special reason
-- (for example: the Bool type)
-- Try to avoid imports from G2 other than G2.Internal.Language.Syntax here!
module G2.Internals.Language.KnownValues where

import G2.Internals.Language.Syntax

data KnownValues = KnownValues {
                   tyInt :: Name
                 , dcInt :: Name

                 , tyFloat :: Name
                 , dcFloat :: Name

                 , tyDouble :: Name
                 , dcDouble :: Name

                 , tyBool :: Name
                 , dcTrue :: Name
                 , dcFalse :: Name

                 , eqTC :: Name
                 , numTC :: Name
                 , ordTC :: Name

                 , eqFunc :: Name
                 , neqFunc :: Name
                 , geFunc :: Name
                 , gtFunc :: Name
                 , ltFunc :: Name
                 , leFunc :: Name
                 } deriving (Show, Eq, Read)