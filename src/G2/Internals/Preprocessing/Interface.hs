module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language.Support
import G2.Internals.Preprocessing.Defunctionalizor
import G2.Internals.Preprocessing.FreeBind
import G2.Internals.Preprocessing.LetFloating
import G2.Internals.Preprocessing.NameCleaner

runPreprocessing :: State -> State
runPreprocessing s =
	let
		s' = cleanNames s
		eenv = freeVarsBind $ expr_env s
		(eenv', ng) = letFloat eenv (name_gen s)
		(eenv'', tenv, ng', ft) = defunctionalize eenv' (type_env s) ng
	in
	s { expr_env = eenv''
	  , type_env = tenv
	  , name_gen = ng'
	  , func_table = ft }