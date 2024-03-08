{-# LANGUAGE  OverloadedStrings, FlexibleContexts #-}
module G2.Execution.InstTypes where


import G2.Language
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E 
import qualified Data.List as L 
import Debug.Trace



generateIds :: NameGen -> Type -> (NameGen, Id)
generateIds ng t = 
    let 
        (tn, ng') = freshSeededString "t" ng 
    in
        (ng', Id tn t)

generateTyForAll :: Id -> Type 
generateTyForAll i@(Id _ t) = TyForAll i t

newType :: NameGen -> Id -> TypeEnv -> (Type, TypeEnv, NameGen)
newType ng i te = 
    let  
        -- getting the typename and type constructor
        (tn, ng') = freshSeededString "T" ng 
        (dc, ng'') = freshSeededString "DC" ng' 

        i_k = typeOf i
        -- getting the arguments of the kind
        ats = argumentTypes i_k
        (ng''', all_ids) = L.mapAccumL generateIds ng'' ats
        -- turn those id (argument of the type) into tyforall and tyfun
        argtys = map generateTyForAll all_ids
        tyforalls' = mkTyApp argtys
        tyapps = i_k : argtys
        tyfuns = TyFun TyLitInt (mkTyApp tyapps)

        nadt = DataTyCon 
        -- the bound_ids are the same ids you get from the generate_arg_type (should rename those into generate new ids)
                    {bound_ids = all_ids
                    ,data_cons = [DataCon dc (TyApp tyforalls' tyfuns)]}
        te' = HM.insert tn nadt te 
    in
     (i_k, te', ng''')

instType :: ASTContainer t Type => NameGen -> State t -> (NameGen, State t)
instType ng st = 
    let 
        is = tyVarIds $ curr_expr st
        (ng', st') = L.foldl' instType' (ng, st) is
    in
    (ng', st')

-- Introducing a new type for a type variable and substituting the variable in the curr_expr
instType' :: ASTContainer t Type => (NameGen, State t) -> Id -> (NameGen, State t)
instType' (ng, st) i =
    let 
        (t,te,ng') = newType ng i (type_env st)
        n = idName i
        eenv' = E.insert n (Var i) (expr_env st)
        st' = st {expr_env = eenv'
                 ,type_env = te}
        st'' = replaceTyVar n t  st'
    in
  (ng',st'')