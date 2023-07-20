{-# LANGUAGE  FlexibleContexts, OverloadedStrings #-}


module G2.Equiv.Uninterpreted where 

import G2.Language
import qualified G2.Language.ExprEnv as E
import Data.Foldable
import Data.Maybe 
import qualified Data.Monoid as DM
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Debug.Trace
import qualified Data.Text as T

-- | Find variables that don't have binding and adjust the epxression environment to treat them as symbolic 
addFreeVarsAsSymbolic :: ExprEnv -> ExprEnv 
addFreeVarsAsSymbolic eenv = let xs = freeVars eenv eenv 
                             in foldl' (flip E.insertSymbolic) eenv xs 

addFreeTypes :: (ASTContainer e Type, ASTContainer e Expr) => e -> TypeEnv -> ExprEnv -> NameGen -> (TypeEnv, ExprEnv, NameGen) 
addFreeTypes e te ee ng = let (te', ng') = freeTypesToTypeEnv (freeTypes te e) ng
                              te'' = HM.union te te'
                              free_dc = HS.toList $ freeDC te'' e 
                              n_te = addDataCons te'' free_dc
                              ee' = addMapping free_dc ee
                           in (n_te, ee', ng')


allDC :: ASTContainer t Expr => t -> HS.HashSet DataCon
allDC = evalASTs allDC' 

allDC' :: Expr -> HS.HashSet DataCon
allDC' e = case e of 
    Data dc -> HS.singleton dc
    Case _ _ _ as ->
            HS.fromList $ mapMaybe (\(Alt am _) -> case am of 
                                                        DataAlt dc _ -> Just dc
                                                        _ -> Nothing) as 
    _ -> HS.empty



freeDC :: ASTContainer e Expr => TypeEnv -> e -> HS.HashSet DataCon
freeDC typeEnv e =
    let al = allDC e
        inTEnv = HS.map (\(DataCon n _) -> n)
               . HS.fromList
               . concatMap dataCon
               . HM.elems $ typeEnv in
    trace ("diff = " ++ show (HS.filter (\(DataCon n _) -> not (HS.member n inTEnv)) al)) HS.filter (\(DataCon n _) -> not (HS.member n inTEnv)) al


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
addDataCon te dc | (TyCon n _):_ <- unTyApp $ returnType dc = 
    let dtc = HM.lookup n te
        adt = case dtc of 
                   Just (DataTyCon ids' dcs) -> DataTyCon {bound_ids = ids', data_cons = dc : dcs}
                   Nothing -> error "addDataCons: cannot find corresponding Name in TypeEnv"
                   Just _ -> error "addDataCons: Not DataTyCon AlgDataTy found"
        in HM.insert n adt te 
addDataCon _ _ = error "addDataCon: Type of DataCon had incorrect form"

-- | addMapping will handle classification between the DataCon and Type
addMapping :: [DataCon] -> ExprEnv -> ExprEnv 
addMapping dcs ee = foldl' addMapping' ee dcs

addMapping' :: ExprEnv -> DataCon -> ExprEnv 
addMapping' ee dc@(DataCon name _) = E.insert name (Data dc) ee


-- | The translation between GHC and g2 didn't have a matching id for the same occurence name
-- so we are using brute force by matching the same occurence name 

dataConMapping :: [DataCon] -> HM.HashMap (T.Text, Maybe T.Text) DataCon
dataConMapping dcs = HM.fromList $ map dataConMapping' dcs 

dataConMapping' :: DataCon -> ((T.Text, Maybe T.Text ), DataCon)
dataConMapping' dc@(DataCon n _) = case n of 
                                        Name t mt _ _-> ((t,mt), dc)
                                        _  -> error "dataConMapping': The dataCon don't have occurence name"

subVars :: ASTContainer e Expr => HM.HashMap (T.Text, Maybe T.Text) DataCon -> e -> e 
subVars m = modifyASTs (subVars' m) 

subVars' :: HM.HashMap (T.Text, Maybe T.Text) DataCon -> Expr -> Expr
subVars' m (Var i) = case i of 
                          Id n _ -> case n of 
                                           Name t mt _ _  -> case HM.lookup (t,mt) m of 
                                                                Just (DataCon n k) -> Data (DataCon n k)
                                                                _ -> error "subVars: can't find a corresponding dataCon from the occurence name, module name"

                          _ -> error "subVars: the type pass in isn't a Name type"  
