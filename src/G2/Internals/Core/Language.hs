module G2.Internals.Core.Language ( module G2.Internals.Core.Language
                                  , module G2.Internals.Core.GenLanguage) where

import G2.Internals.Core.GenLanguage

type Name = String

type State = GenState Name (PrimDataCon Name)

type TEnv = GenTEnv Name (PrimDataCon Name)
type EEnv = GenEEnv Name (PrimDataCon Name)
type SymLinkTable = GenSymLinkTable Name (PrimDataCon Name)
type FuncInterpTable = GenFuncInterpTable Name

type Expr = GenExpr Name (PrimDataCon Name)

type DataCon = GenDataCon Name (PrimDataCon Name)

type Type = GenType Name (PrimDataCon Name)

type Alt = GenAlt Name (PrimDataCon Name)

type PathCond = GenPathCond Name (PrimDataCon Name)