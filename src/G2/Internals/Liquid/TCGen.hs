module G2.Internals.Liquid.TCGen where

import G2.Internals.Language

import qualified Data.Map as M

createLHEq :: State -> (State, Walkers)
createLHEq s@(State { expr_env = eenv
					, type_env = tenv
					, name_gen = ng }) =
	let
		tenv' = M.toList tenv

		(eenv', ng', w) = createFuncs eenv ng tenv' M.empty (lhEqName . fst) lhEqStore lhEqExpr
	in
	(s { expr_env = eenv', name_gen = ng' }, w)

lhEqName :: Name -> Name
lhEqName (Name n _ _) = Name ("lhEqName" ++ n) Nothing 0

lhEqStore :: (Name, AlgDataTy) -> Name -> Walkers -> Walkers
lhEqStore (n, adt) n' w =
    let
        bn = bound_names adt
        bnt = map (TyVar . flip Id TYPE) bn
        bnf = map (\b -> TyFun b b) bnt

        base = TyFun (TyConApp n []) (TyConApp n [])

        t = foldr TyFun base (bnt ++ bnf)
        i = Id n' t
    in
    M.insert n i w

lhEqExpr :: Walker -> (Name, AlgDataTy) -> NameGen -> (Expr, NameGen)
lhEqExpr = undefined