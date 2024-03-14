{-# LANGUAGE  OverloadedStrings, FlexibleContexts #-}
module G2.Execution.InstTypes where


import G2.Language
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E 
import qualified Data.List as L 
import Debug.Trace
import Data.Foldable (foldl')



generateIds :: NameGen -> Type -> (NameGen, Id)
generateIds ng t = 
    let 
        (tn, ng') = freshSeededString "t" ng 
    in
    (ng', Id tn t)

newType :: NameGen -> Id -> TypeEnv -> (Type, TypeEnv, NameGen)
newType ng i te = 
    let  
        -- getting the typename and type constructor
        (tn, ng') = freshSeededString "T" ng 
        (dc, ng'') = freshSeededString "DC" ng' 

        i_k = typeOf i
        ty = TyCon tn i_k
        -- getting the arguments of the kind
        (ng''', all_ids) = L.mapAccumL generateIds ng'' (argumentTypes $ PresType i_k)
        -- make those id into tyvars
        -- make a nested Tyapp centered at ty and
        -- the centered of tyforalls is the result from the previous lines
        tys = ty : map TyVar all_ids
        tyapps = mkTyApp tys
        tyfuns = TyFun TyLitInt tyapps
        
        tyforall = foldl' (flip TyForAll) tyfuns all_ids

        nadt = DataTyCon 
        -- the bound_ids are the same ids you get from the generate_arg_type (should rename those into generate new ids)
                    {bound_ids = all_ids
                    ,data_cons = [DataCon dc tyforall]}
        te' = HM.insert tn nadt te 
    in
    trace ("all_ids = " ++ show all_ids ++ "\ntyforall = " ++ show tyforall)
    (ty, te', ng''')

instType :: ASTContainer t Type => NameGen -> State t -> (NameGen, State t)
instType ng st = 
    let 
        is = tyVarIds $ curr_expr st
        (ng', st') = L.foldl' instType' (ng, st) is
    in
    trace ("curr_expr = " ++ show (curr_expr st')) (ng', st')

-- Introducing a new type for a type variable and substituting the variable in the curr_expr
instType' :: ASTContainer t Type => (NameGen, State t) -> Id -> (NameGen, State t)
instType' (ng, st) i =
    let 
        (t,te,ng') = newType ng i (type_env st)
        n = idName i
        eenv' = E.insert n (Var i) (expr_env st)
        st' = st {expr_env = eenv'
                 ,type_env = te}
        st'' = replaceTyVar n t st'
    in
    trace ("i = " ++ show i ++ "\nt = " ++ show t) (ng',st'')