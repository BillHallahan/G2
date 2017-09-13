module G2.Internals.Preprocessing.FreeBind (freeVarsBind) where

-- We bind all free variables in the Expr Env to symbolic variables.
-- This prevents errors when Let Floating, if (for example) the Num typeclass
-- dictionary is not technically in scope

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

freeVarsBind :: State -> State
freeVarsBind s@State {expr_env = eenv} =
	let
		fv = freeVars eenv eenv
		eenv' = foldr (\i -> E.insertSymbolic (idName i) i) eenv fv
	in
	s {expr_env = eenv'}