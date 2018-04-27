module G2.Internals.Liquid.TCValues where

import G2.Internals.Language.Naming
import G2.Internals.Language.Syntax

data TCValues = TCValues { lhTC :: Name
                         , lhEq :: Name
                         , lhNe :: Name

                         , lhLt :: Name
                         , lhLe :: Name
                         , lhGt :: Name
                         , lhGe :: Name

                         , lhPP :: Name } deriving (Eq, Show, Read)

instance Named TCValues where
    names tcv = [lhTC tcv, lhEq tcv, lhNe tcv, lhLt tcv, lhGt tcv, lhGe tcv, lhPP tcv]
    rename old new tcv = TCValues { lhTC = rename old new $ lhTC tcv
                                  , lhEq = rename old new $ lhEq tcv
                                  , lhNe = rename old new $ lhNe tcv
                                    
                                  , lhLt = rename old new $ lhLt tcv
                                  , lhLe = rename old new $ lhLe tcv
                                  , lhGt = rename old new $ lhGt tcv
                                  , lhGe = rename old new $ lhGe tcv

                                  , lhPP = rename old new $ lhPP tcv }
