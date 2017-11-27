module G2.Internals.Liquid.CreateFuncs where

import G2.Internals.Language

import qualified Data.Map as M

-- | createEqPreds
-- For ADTs over which equality can be defined (i.e. they have no function
-- arguments) we generate functions to check conjmstructor wise equality-
-- the results of these functions, and the functions obtained from a
-- deriving Eq should be equivalent
createEqPreds :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createEqPreds eenv tenv ng =
	let
		tenv' = M.filter (all (not . hasFuncType) . concatMap dataConArgs . dataCon) tenv
	in
	createEqPreds' eenv (M.toList tenv') ng M.empty

createEqPreds' :: ExprEnv -> [(Name, AlgDataTy)] -> NameGen -> Walkers-> (ExprEnv, NameGen, Walkers)
createEqPreds' eenv [] ng  w = (eenv, ng, w)
createEqPreds' eenv ((n, AlgDataTy ns ts):xs) ng w = undefined