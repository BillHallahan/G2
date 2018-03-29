module G2.Internals.Language.Located (Located (..)) where

import G2.Internals.Language.Syntax

class Located l where
    loc :: l -> Maybe Loc

instance Located Name where
    loc (Name _ _ _ l) = l

instance Located Id where
    loc (Id n _) = loc n