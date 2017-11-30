module G2.Internals.Liquid.CreateFuncs where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Liquid.Primitives

import qualified Data.Map as M
import Data.Maybe

-- | createEqPreds
-- For ADTs over which equality can be defined (i.e. they have no function
-- arguments) we generate functions to check conjmstructor wise equality-
-- the results of these functions, and the functions obtained from a
-- deriving Eq should be equivalent
createEqPreds :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, NameGen, Walkers)
createEqPreds eenv tenv ng =
    let
        tenv' = M.filter (all (not . hasFuncType) . concatMap dataConArgs . dataCon) tenv

        (walkers, ng') = createEqWalkers (M.toList tenv') ng
    in
    createEqPreds' eenv (M.toList tenv') ng' walkers

createEqPreds' :: ExprEnv -> [(Name, AlgDataTy)] -> NameGen -> Walkers -> (ExprEnv, NameGen, Walkers)
createEqPreds' eenv [] ng  w = (eenv, ng, w)
createEqPreds' eenv ((n, DataTyCon ns dc):xs) ng w =
    let
        (e, ng') = createEqPred eenv (TyConApp n []) ns dc ng w
    
        en = M.lookup n w

        eenv' = fmap (\(Id en' _) -> E.insert en' e eenv) en
    in
    createEqPreds' (maybe eenv id eenv') xs ng' w

-- | createEqPred
-- Creates a single equality checker.
createEqPred :: ExprEnv -> Type -> [Name] -> [DataCon] -> NameGen -> Walkers -> (Expr, NameGen)
createEqPred eenv t ns dc ng w =
    let
        (fe, i1, i2, ng') = createEqPredLams t ng

        (ib, ng'') = freshId t ng'

        (alts, ng''') = mapNG (createEqPredAlts eenv i1 i2 w) dc ng''

        e = Case (Var i1) ib alts
    in
    (fe e, ng''')

createEqPredLams :: Type -> NameGen -> (Expr -> Expr, Id, Id, NameGen)
createEqPredLams t ng =
    let
        (i1, ng') = freshId t ng
        (i2, ng'') = freshId t ng'
    in
    (Lam i1 . Lam i2, i1, i1, ng'')

createEqPredAlts :: ExprEnv -> Id -> Id -> Walkers -> DataCon -> NameGen -> (Alt, NameGen)
createEqPredAlts eenv i1 i2 w dc@(DataCon _ _ ts) ng =
    let
        (is, ng') = freshIds ts ng

        (is', ng'') = freshIds ts ng'

        (i2b, ng''') = freshId (typeOf i2) ng''

        e' = foldr (\e e'-> mkApp [mkAnd eenv, e, e']) mkTrue $ map (uncurry (createEqPredBranching eenv w)) $ zip is is'

        e = Case (Var i2) i2b 
            [ Alt (DataAlt dc is') e'
            , Alt Default (Lit (LitBool False))]
    in
    (Alt (DataAlt dc is) e, ng''')

createEqPredBranching :: ExprEnv -> Walkers -> Id -> Id -> Expr
createEqPredBranching eenv w i1 i2 =
    let
        t = typeOf i1
    in
    case t of
        TyConApp n _ -> App (App (Var $ fromJust $ M.lookup n w) (Var i1)) $ Var i2 
        _ -> mkLHEq (Var i1) (Var i2) 

-- | createEqWalkers
-- Creates the names map of all equality checkers.  They might need to be
-- mutually recursive, so it is important to know all the names in advance.
createEqWalkers :: [(Name, AlgDataTy)] -> NameGen -> (Walkers, NameGen)
createEqWalkers nadts ng = createEqWalkers' nadts ng M.empty

createEqWalkers' :: [(Name, AlgDataTy)] -> NameGen -> Walkers -> (Walkers, NameGen)
createEqWalkers' [] ng w = (w, ng)
createEqWalkers' ((n, DataTyCon ns _):xs) ng w =
    let
        (i, ng') = eqWalkerId n ns ng
    in
    createEqWalkers' xs ng' (M.insert n i w)

eqWalkerId :: Name -> [Name] -> NameGen -> (Id, NameGen)
eqWalkerId n ns ng =
    let
        (n', ng') = freshSeededName n ng
        t = TyFun (TyConApp n []) $ TyFun (TyConApp n []) TyBool
    in
    (Id n' t, ng')