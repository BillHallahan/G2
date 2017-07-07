module G2.Internals.Core.Language ( module G2.Internals.Core.Language
						   	      , module G2.Internals.Core.GenLanguage) where

import G2.Internals.Core.GenLanguage

type Name = String

type State = GenState Name

type TEnv = GenTEnv Name
type EEnv = GenEEnv Name
type SymLinkTable = GenSymLinkTable Name
type FuncInterpTable = GenFuncInterpTable Name

type Expr = GenExpr Name

type Const = GenConst Name

type DataCon = GenDataCon Name

type Type = GenType Name

type Alt = GenAlt Name

type PathCond = GenPathCond Name