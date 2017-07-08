module G2.Internals.Translation.Language
    ( module G2.Internals.Translation.Language
    , module G2.Internals.Core.GenLanguage) where

import G2.Internals.Core.GenLanguage

type TName = (String, Int)

type TTEnv = GenTEnv TName TName
type TEEnv = GenEEnv TName TName

type TExpr = GenExpr TName TName

type TDataCon = GenDataCon TName TName

type TType = GenType TName TName

type TAlt = GenAlt TName TName
