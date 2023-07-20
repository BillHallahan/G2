{-# LANGUAGE  FlexibleContexts, OverloadedStrings #-}


module G2.Equiv.Uninterpreted where 

import G2.Language
import qualified G2.Language.ExprEnv as E
import Data.Foldable
import Data.Maybe 
import qualified Data.Monoid as DM
import qualified Data.HashMap.Lazy as HM 
import Data.List  
import qualified G2.Language.TypeEnv as T

-- | Find variables that don't have binding and adjust the epxression environment to treat them as symbolic 
addFreeVarsAsSymbolic :: ExprEnv -> ExprEnv 
addFreeVarsAsSymbolic eenv = let xs = freeVars eenv eenv 
                             in foldl' (flip E.insertSymbolic) eenv xs 

addFreeTypes :: (ASTContainer e Type, ASTContainer e Expr) => e -> TypeEnv -> ExprEnv -> NameGen -> (TypeEnv, ExprEnv, NameGen) 
addFreeTypes e te ee ng = let (te', ng') = freeTypesToTypeEnv (freeTypes te e) ng
                              te'' = HM.union te te'
                              n_te = addDataCons te'' (freeDC te' e) 
                              ee' = addMapping te'' e ee
                           in (n_te, ee', ng')


allDC :: ASTContainer t Expr => t -> [DataCon]
allDC = evalASTs allDC' 

allDC' :: Expr -> [DataCon]
allDC' e = case e of 
    Data dc -> [dc] 
    Case _ _ _ as -> mapMaybe (\(Alt am _) -> case am of 
                                                        DataAlt dc _ -> Just dc
                                                        _ -> Nothing) as 
    _ -> []



freeDC :: ASTContainer e Expr => TypeEnv -> e -> [DataCon]
freeDC typeEnv e = allDC e \\ (concatMap dataCon . HM.elems $ typeEnv)

allTypes :: ASTContainer t Type => t -> [(Name, Kind)]
allTypes = evalASTs allTypes' 

allTypes' :: Type -> [(Name, Kind)]
allTypes' t = case t of 
        TyCon n k -> [(n,k)]
        _ -> []


freeTypes :: ASTContainer t Type => TypeEnv -> t -> [(Name, Kind)]
freeTypes typeEnv t = HM.toList $ HM.difference (HM.fromList $ allTypes t) typeEnv 


-- | we getting "free" typesnames and insert it into the TypeEnv with a "uninterprted " dataCons 
-- Uninterpreted means there are potentially unlimited amount of datacons for a free type
freeTypesToTypeEnv :: [(Name,Kind)] -> NameGen -> (TypeEnv, NameGen)
freeTypesToTypeEnv nks ng = 
    let (adts, ng') = mapNG freeTypesToTypeEnv' nks ng 
    in  (HM.fromList adts, ng') 

freeTypesToTypeEnv' :: (Name, Kind) -> NameGen -> ( (Name, AlgDataTy), NameGen)
freeTypesToTypeEnv' (n,k) ng =
    let (bids, ng') = freshIds (argumentTypes $ PresType k) ng 
        (dcs,ng'') = unknownDC ng' n k bids
        n_adt = (n, DataTyCon {bound_ids = bids,
                               data_cons = [dcs]})
        in (n_adt, ng'')

unknownDC :: NameGen -> Name -> Kind -> [Id] -> (DataCon, NameGen)
unknownDC ng n@(Name occn _ _ _) k is =
    let tc = TyCon n k 
        tv = map TyVar is
        ta = foldl' TyApp tc tv 
        ti = TyLitInt `TyFun` ta 
        tfa = foldl' (flip TyForAll) ti is
        (dc_n, ng') = freshSeededString ("Unknown" DM.<> occn) ng   
        in (DataCon dc_n tfa, ng')

-- | add free Datacons into the TypeEnv at the appriorpate Type)
addDataCons :: TypeEnv -> [DataCon] -> TypeEnv
addDataCons = foldl' addDataCon

addDataCon :: TypeEnv -> DataCon -> TypeEnv
addDataCon te dc = 
    let (TyCon n _):_ = unTyApp $ returnType dc
        dtc = HM.lookup n te
        adt = case dtc of 
                   Just (DataTyCon ids' dcs) -> DataTyCon {bound_ids = ids', data_cons = dc : dcs}
                   Nothing -> error "addDataCons: cannot find corresponding Name in TypeEnv"
        in HM.insert n adt te 

addMapping :: ASTContainer e Expr => TypeEnv -> e -> ExprEnv -> ExprEnv 
addMapping te e ee = foldl' addMapping' ee (freeDC te e) 

addMapping' :: ExprEnv -> DataCon -> ExprEnv 
addMapping' ee dc@(DataCon name _) = E.insert name (Data dc) ee