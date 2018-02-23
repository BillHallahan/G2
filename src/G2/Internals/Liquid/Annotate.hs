module G2.Internals.Liquid.Annotate (annotateCases) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

annotateCases :: State h t -> State h t
annotateCases s@(State {expr_env = eenv}) = s {expr_env = E.mapWithKey annotateCases' eenv}

annotateCases' :: Name -> Expr -> Expr
annotateCases' n c@(Case e i a) =
	Annotation n $ Case (annotateCases' n e) i (modifyContainedASTs (annotateCases' n) a)
annotateCases' n e = modifyChildren (annotateCases' n) e