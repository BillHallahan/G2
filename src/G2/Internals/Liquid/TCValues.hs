module G2.Internals.Liquid.TCValues where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

-- | Stores variable names that are used in the LH encoding.
-- There are two reasons a name might exist:
--   (1) It corresponds to something that only makes sense in the context of LH
--       (i.e. the LH typeclass)
--   (2) It is a copy of a function that normally exists, but that copy has no assertion added. 
data TCValues = TCValues { lhTC :: Name
                         , lhNumTC :: Name
                         , lhOrdTC :: Name

                         , lhEq :: Name
                         , lhNe :: Name

                         , lhLt :: Name
                         , lhLe :: Name
                         , lhGt :: Name
                         , lhGe :: Name

                         , lhPlus :: Name
                         , lhMinus :: Name
                         , lhTimes :: Name
                         , lhDiv :: Name
                         , lhNegate :: Name
                         , lhMod :: Name
                         , lhFromInteger :: Name

                         , lhNumOrd :: Name

                         , lhAnd :: Name
                         , lhOr :: Name

                         , lhPP :: Name } deriving (Eq, Show, Read)

instance Named TCValues where
    names tcv = [ lhTC tcv
                , lhNumTC tcv
                , lhOrdTC tcv
                , lhEq tcv
                , lhNe tcv

                , lhLe tcv
                , lhLt tcv
                , lhGt tcv
                , lhGe tcv
                
                , lhPlus tcv
                , lhMinus tcv
                , lhTimes tcv
                , lhDiv tcv
                , lhNegate tcv
                , lhMod tcv
                , lhFromInteger tcv
                , lhNumOrd tcv

                , lhAnd tcv
                , lhOr tcv

                , lhPP tcv]

    rename old new tcv = TCValues { lhTC = rename old new $ lhTC tcv
                                  , lhNumTC = rename old new $ lhNumTC tcv
                                  , lhOrdTC = rename old new $ lhOrdTC tcv
                                  , lhEq = rename old new $ lhEq tcv
                                  , lhNe = rename old new $ lhNe tcv
                                    
                                  , lhLt = rename old new $ lhLt tcv
                                  , lhLe = rename old new $ lhLe tcv
                                  , lhGt = rename old new $ lhGt tcv
                                  , lhGe = rename old new $ lhGe tcv

                                  , lhPlus = rename old new $ lhPlus tcv
                                  , lhMinus = rename old new $ lhMinus tcv
                                  , lhTimes = rename old new $ lhTimes tcv
                                  , lhDiv = rename old new $ lhDiv tcv
                                  , lhNegate = rename old new $ lhNegate tcv
                                  , lhMod = rename old new $ lhMod tcv
                                  , lhFromInteger = rename old new $ lhFromInteger tcv
                                  , lhNumOrd = rename old new $ lhNumOrd tcv

                                  , lhAnd = rename old new $ lhAnd tcv
                                  , lhOr = rename old new $ lhOr tcv

                                  , lhPP = rename old new $ lhPP tcv }
