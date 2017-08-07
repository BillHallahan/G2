module G2.Internals.Language.Naming (Renamer) where

import G2.Internals.Language.Syntax

newtype Renamer = Renamer [Name]

instance Show Renamer where

instance Eq Renamer where

instance Read Renamer where