module G2.Internals.Translation.Language ( module G2.Internals.Translation.Language
						   	    	     , module G2.Internals.Core.GenLanguage) where

import G2.Internals.Core.GenLanguage

type TName = (String, Int)

type TTEnv = GenTEnv TName
type TEEnv = GenEEnv TName

type TExpr = GenExpr TName

type TDataCon = GenDataCon TName

type TType = GenType TName

type TAlt = GenAlt TName