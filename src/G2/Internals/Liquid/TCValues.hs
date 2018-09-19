module G2.Internals.Liquid.TCValues where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

data TCValues = TCValues { lhTC :: Name
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

                         , lhPP :: Name } deriving (Eq, Show, Read)

instance Named TCValues where
    names tcv = [ lhTC tcv
                , lhOrdTC tcv
                , lhEq tcv
                , lhNe tcv
                , lhLt tcv
                , lhGt tcv
                , lhGe tcv
                
                , lhPlus tcv
                , lhMinus tcv
                , lhTimes tcv
                , lhDiv tcv
                , lhNegate tcv
                , lhMod tcv

                , lhPP tcv]
    rename old new tcv = TCValues { lhTC = rename old new $ lhTC tcv
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

                                  , lhPP = rename old new $ lhPP tcv }
