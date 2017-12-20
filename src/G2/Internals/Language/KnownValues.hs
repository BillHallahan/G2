-- We define a datatype to hol the names of other data types we know should
-- exist, and that we care about for some special reason
-- (for example: the Bool type)
-- Try to avoid imports from G2 other than G2.Internal.Language.Syntax here!
module G2.Internals.Language.KnownValues where

import G2.Internals.Language.Syntax

data KnownValues = KnownValues {
                   tyInt :: Name
                 , tyFloat :: Name
                 , tyDouble :: Name

                 , tyBool :: Name
                 , dcTrue :: Name
                 , dcFalse :: Name
                 } deriving (Show, Eq, Read)