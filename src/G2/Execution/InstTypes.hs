{-# LANGUAGE  OverloadedStrings #-}
module G2.Execution.InstTypes where


import G2.Language
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E 
import qualified Data.List as L 

newType :: NameGen -> TypeEnv -> (Type, TypeEnv, NameGen)
newType ng te = 
    let  
        -- getting the typename and type constructor
        (tn, ng') = freshSeededString "T" ng 
        (dc, ng'') = freshSeededString "DC" ng' 
        -- creating a new algdatatype so we can insert into the 
        nadt = DataTyCon 
                    {bound_ids = []
                    ,data_cons = [DataCon dc (TyFun TyLitInt (TyCon tn TYPE))]}
        te' = HM.insert tn nadt te 
    in
        (TyCon tn TYPE, te', ng'')

instType :: NameGen -> State t -> (State t, NameGen)
instType ng st = 
    let 
        is = tyVarIds $ curr_expr st
        (st', ng') = L.foldl' instType' (st, ng) is
    in
        (st', ng')

-- Introducing a new type for a type variable and substituting the variable in the curr_expr
instType' :: (State t, NameGen) -> Id -> (State t, NameGen)
instType' (st, ng) i =
    let 
        (t,te,ng') = newType ng (type_env st)
        n = idName i
        eenv' = E.insert n (Var i) (expr_env st)
        st' = st {expr_env = eenv'
                 ,type_env = te}
        cexpr = replaceTyVar n t (curr_expr st')
        st'' = st' {curr_expr = cexpr}
    in
        (st'',ng')