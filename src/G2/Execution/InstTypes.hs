{-# LANGUAGE  OverloadedStrings, FlexibleContexts #-}
module G2.Execution.InstTypes (instTypeRed) where


import G2.Language
import qualified Data.HashMap.Lazy as HM
import qualified G2.Language.ExprEnv as E 
import qualified Data.List as L 

import Data.Foldable (foldl')
import G2.Language.ExprEnv (isSymbolic)
import G2.Language.AlgDataTy 
import G2.Execution



generateIds :: NameGen -> Type -> (NameGen, Id)
generateIds ng t = 
    let 
        (tn, ng') = freshSeededString "t" ng 
    in
    (ng', Id tn t)

newType :: NameGen -> Id -> TypeEnv -> (Type, TypeEnv, NameGen)
newType ng i te = 
    let  
        (tn, ng') = freshSeededString "T" ng 
        (dc, ng'') = freshSeededString "DC" ng' 

        i_k = typeOf i
        ty = TyCon tn i_k
        (ng''', all_ids) = L.mapAccumL generateIds ng'' (argumentTypes $ PresType i_k)
        
        tys = ty : map TyVar all_ids
        tyapps = mkTyApp tys
        tyfuns = TyFun TyLitInt tyapps
        tyforall = foldl' (flip TyForAll) tyfuns all_ids

        nadt = DataTyCon 
                    { bound_ids = all_ids
                    , data_cons = [DataCon dc tyforall]
                    , adt_source = ADTG2Generated }
        te' = HM.insert tn nadt te 
    in
    (ty, te', ng''')
    
-- | We want to find all the type variable from curr_expr and replace them with symbolic variable
instType :: ASTContainer t Type => State t -> Bindings -> (State t, Bindings)
instType st b@(Bindings { name_gen = ng, input_names = ins }) = 
    let 
        is = tyVarIds $ map (\n -> E.lookup n (expr_env st)) ins
        (ng', st') = L.foldl' instType' (ng, st) is
        b'  = b {name_gen = ng'}
    in
      (st', b') 

-- Introducing a new type for a type variable and substituting the variable in the curr_expr
instType' :: ASTContainer t Type => (NameGen, State t) -> Id -> (NameGen, State t)
instType' (ng, st) i 
    | isSymbolic (idName i) (expr_env st) =
        let 
            (t,te,ng') = newType ng i (type_env st)
            n = idName i
            eenv' = E.insert n (Type t) (expr_env st)
            st' = st {expr_env = eenv'
                    ,type_env = te}
            st'' = replaceTyVar n t st'
        in
         (ng',st'')
    | otherwise = (ng, st)
        
-- define a new reducer that calls your instType on your onAccept function
instTypeRed :: (ASTContainer t Type, Monad m) => Reducer m () t
instTypeRed  = (mkSimpleReducer
                        (\_ -> ())
                        (\rv s b -> return (NoProgress, [(s , rv)], b)) )
                        {
                         onAccept = \s b _ -> return (instType s b)} 