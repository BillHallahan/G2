-- This module generates functions in the expr_env that walk over the whole structure of an ADT.
-- This forces evaluation of the ADT

module G2.Internals.Initialization.CreateWalks (createWalks) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

import qualified Data.Map as M
import Data.Maybe

createWalks :: ExprEnv -> TypeEnv -> NameGen -> (ExprEnv, Walkers, NameGen)
createWalks eenv tenv ng = 
    let
        tenv_list = M.toList tenv
        (walk_names, ng') = freshSeededNames (map (\(Name n m _, _) -> Name ("walk" ++ n) m 0) tenv_list) ng
        tenv_list' = map (\(n, (tn, t)) -> (n, tn, t)) (zip walk_names tenv_list)

        tyToWalk = map (\(t, w) -> (t, Id w (TyFun (TyConApp t []) (TyConApp t [])))) $ zip (map fst tenv_list) (walk_names)

        (walks, ng'') = createWalk tenv_list' tyToWalk ng'

        eenv' = foldr (uncurry E.insert) eenv walks
    in
    (eenv', M.fromList tyToWalk, ng'')

createWalk :: [(Name, Name, AlgDataTy)] -> [(Name, Id)] -> NameGen -> ([(Name, Expr)], NameGen)
createWalk [] _ ng = ([], ng)
createWalk ((n, tn, AlgDataTy _ dc):na) ns ng =
    let
        (alts, ng2) = fstDataConAltMatch dc ns ng

        (l_bind, ng3) = freshName ng2
        l_bind_id = Id l_bind (TyConApp tn [])
        l_var = Var l_bind_id

        (c_bind, ng4) = freshName ng3
        c_bind_id = Id c_bind (TyConApp tn [])
        
        c = Lam l_bind_id $ Case l_var c_bind_id alts

        (t, ng5) = createWalk na ns ng4
    in
    ((n, c):t, ng5)

fstDataConAltMatch :: [DataCon] -> [(Name, Id)] -> NameGen -> ([Alt], NameGen)
fstDataConAltMatch [] _ ng = ([], ng)
fstDataConAltMatch (dc@(DataCon _ _ ts):dcs) ns ng =
    let
        (arg_names, ng1) = freshNames (length ts) ng
        arg_ids = map (uncurry Id) (zip arg_names ts)

        am = DataAlt dc arg_ids
        (e, ng3) = sndDataConAltMatch arg_ids ns (Data dc) ng1

        alt = Alt am e

        (t, ng4) = fstDataConAltMatch dcs ns ng3
    in
    (alt:t, ng4)
fstDataConAltMatch (_:xs) ns ng = fstDataConAltMatch xs ns ng

sndDataConAltMatch :: [Id] -> [(Name, Id)] -> Expr -> NameGen -> (Expr, NameGen)
sndDataConAltMatch [] _ dc ng = (dc, ng)
sndDataConAltMatch (i@(Id _ t):xs) ns dc ng =
    let
        (b, ng') = freshName ng
        b_id = Id b t

        case_e = case t of
                    TyConApp n' _ -> let f = fromJust $ lookup n' ns in Case (App (Var f) (Var i)) b_id
                    _ -> Case (Var i) b_id

        dc' = App dc (Var b_id)

        (e, ng'') = sndDataConAltMatch xs ns dc' ng'

        am = [Alt Default e]
    in
    (case_e am, ng'')