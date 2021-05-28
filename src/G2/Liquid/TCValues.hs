module G2.Liquid.TCValues where

import G2.Language.Naming
import G2.Language.Syntax

-- | Stores variable names that are used in the LH encoding.
-- There are two reasons a name might exist:
--   (1) It corresponds to something that only makes sense in the context of LH
--       (i.e. the LH typeclass)
--   (2) It is a copy of a function that normally exists, but that copy has no assertion added.
--   (3) We only care about the specific name in LH code (the Set data type) 
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
                         , lhToInteger :: Name

                         , lhFromRational :: Name

                         , lhToRatioFunc :: Name

                         , lhNumOrd :: Name

                         , lhAnd :: Name
                         , lhOr :: Name
                         , lhNot :: Name

                         , lhImplies :: Name
                         , lhIff :: Name

                         , lhPP :: Name

                         , lhSet :: Maybe Name } deriving (Eq, Show, Read)

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

                , lhToInteger tcv

                , lhFromRational tcv

                , lhToRatioFunc tcv

                , lhNumOrd tcv

                , lhAnd tcv
                , lhOr tcv
                , lhNot tcv

                , lhImplies tcv
                , lhIff tcv

                , lhPP tcv] ++ maybe [] (:[]) (lhSet tcv)

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
                                  , lhToInteger = rename old new $ lhToInteger tcv

                                  , lhFromRational = rename old new $ lhFromRational tcv
                                  
                                  , lhToRatioFunc = rename old new $ lhToRatioFunc tcv

                                  , lhNumOrd = rename old new $ lhNumOrd tcv

                                  , lhAnd = rename old new $ lhAnd tcv
                                  , lhOr = rename old new $ lhOr tcv
                                  , lhNot = rename old new $ lhNot tcv

                                  , lhImplies = rename old new $ lhImplies tcv
                                  , lhIff = rename old new $ lhIff tcv

                                  , lhPP = rename old new $ lhPP tcv

                                  , lhSet = rename old new $ lhSet tcv }
