module G2.Internals.Initialization.Interface where

import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Initialization.Defunctionalizor
import G2.Internals.Initialization.FreeBind
import G2.Internals.Initialization.LetFloating

runInitialization :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, TypeEnv, NameGen, FuncInterps)
runInitialization eenv tenv ng =
	let
		eenv' = freeVarsBind eenv
		(eenv'', ng') = letFloat eenv' ng
		(eenv''', tenv', ng'', ft) = defunctionalize eenv'' tenv ng'
	in
	(eenv''', tenv', ng'', ft)