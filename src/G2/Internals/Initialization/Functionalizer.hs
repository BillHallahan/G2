-- For each higher order type, for example a -> b in:
--     (a -> b) -> c
-- we introduce a new Apply Type:
--     data AT = F | G | ...
-- where each constructor, F, G, ... cooresponds to some function f, g, ...
-- of type a -> b in the expression environment.

-- For each of these Apply Types, we introduce an ApplyFunction, to map
-- the data constructors to the cooresponding functions:
--      applyFunction :: AT -> (a -> b)
--      applyFunction F = f
--      applyFunction G = g
--      ...

-- We recursively define functionalizable ADTs as ADTs which either:
--      (1) Have a function parameter
--      (2) Have a functionalizable ADT as a parameter
-- For each functionalizable ADTs, for example:
--      data D = D (a -> b)
-- we create a new applied datatype:
--      data D' = D' AT
-- and a function:
--      mapDataType :: D' -> D
-- which makes use of applyFunction

-- This allows us to symbolically choose some constructor for the ApplyType
-- with the SMT solver, but immediately convert it to the cooresponding expression
-- in the evaluator.  This way, we don't have to deal with issues with lambda
-- expressions partial evaluation, and a full program transformation that would
-- arise with full defunctionalization, but we still can vary any symbolic
-- higher order functions over all options in the expression environment.

{-# LANGUAGE OverloadedStrings #-}

module G2.Internals.Initialization.Functionalizer (functionalize) where

import G2.Internals.Language
import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E

import Data.List
import qualified Data.Map as M

functionalize :: TypeEnv -> ExprEnv -> NameGen -> [Type] -> [Name]
              -> (TypeEnv, ExprEnv, FuncInterps, AT.ApplyTypes, NameGen)
functionalize tenv eenv ng ts tgtNames =
    let
        -- Get names for all need apply type
        types = (filter isTyFun ts) ++ (nubBy (.::.) $
                argTypesTEnv tenv ++ E.higherOrderExprs eenv)
        (appT, ng2) = applyTypeNames ng types

        -- Update the expression and  type environments with apply types
        (tenv2, eenv2, fi, at, ng3) = mkApplyFuncAndTypes tenv eenv ng2 appT tgtNames

        -- Get all adts that are functionalizable
        funcADTs = functionalizableADTs tenv

        -- create walkers over the functionalizable adts
        (tenv3, eenv3, at2, ng4) = functionalizableADTsMaps funcADTs tenv2 eenv2 at ng3
    in
    (tenv3, eenv3, fi, at2, ng4)


-- creates ApplyType names for the given types
applyTypeNames :: NameGen -> [Type] -> ([(Type, Name)], NameGen)
applyTypeNames ng ts = 
    let
        (applyNames, ng') = freshSeededStrings (replicate (length ts) "applyTy") ng
    in
    (zip ts applyNames, ng')

-- Updates the ExprEnv and TypeEnv with ApplyTypes and Apply Functions
-- creates FuncInterps and ApplyTypes tables
mkApplyFuncAndTypes :: TypeEnv -> ExprEnv -> NameGen -> [(Type, Name)] -> [Name] ->
                       (TypeEnv, ExprEnv, FuncInterps, AT.ApplyTypes, NameGen)
mkApplyFuncAndTypes tenv eenv ng tyn tgtNames = 
    let
        eenv' = E.filterWithKey (\n _ -> n `elem` tgtNames) eenv
        -- This just gets passed around unmodified in mkApplyFuncTypes'
        -- but precomputing is faster
        funcT = M.toList $ E.map' typeOf eenv'
    in
    mkApplyFuncAndTypes' tenv eenv ng tyn funcT (FuncInterps M.empty) (AT.empty)

mkApplyFuncAndTypes' :: TypeEnv -> ExprEnv -> NameGen -> [(Type, Name)]
                     -> [(Name, Type)] -> FuncInterps -> AT.ApplyTypes
                     -> (TypeEnv, ExprEnv, FuncInterps, AT.ApplyTypes, NameGen)
mkApplyFuncAndTypes' tenv eenv ng [] _ fi at = (tenv, eenv, fi, at, ng)
mkApplyFuncAndTypes' tenv eenv ng ((t, n):xs) funcT (FuncInterps fi) at =
    let
        funcFolds = foldr (\(n', t') accs ->
                            case specializes M.empty t t' of
                              (True, m) -> (n', t', m) : accs
                              (False, _) -> accs)
                          [] funcT

        funcs = map (\(n', _, _) -> n') funcFolds

        -- Update type environment
        (applyCons, ng2) = freshSeededNames funcs ng
        dcs = map (\dcn -> DataCon dcn (TyConApp n []) []) applyCons
        adt = DataTyCon [] dcs
        tenv2 = M.insert n adt tenv

        -- Update Func Interps
        applyToFunc = zip applyCons (zip funcs (repeat StdInterp))
        fi' = foldr (uncurry M.insert) fi applyToFunc

        -- ApplyFunc Name
        (applyFuncN, ng3) = freshSeededString "applyFunc" ng2

        -- Update Apply Types
        applyFunc = Id applyFuncN (TyFun (TyConApp n []) t)
        at2 = AT.insert t n applyFunc at

        -- Update expression enviroment
        (expr, ng4) = mkApplyTypeMap ng3 (zip applyCons funcFolds) (TyConApp n []) t
        eenv2 = E.insert applyFuncN expr eenv
    in
    mkApplyFuncAndTypes' tenv2 eenv2 ng4 xs funcT (FuncInterps fi') at2

-- Makes a function to map the apply types to the cooresponding Apply Functions
mkApplyTypeMap :: NameGen -> [(Name, (Name, Type, M.Map Name Type))]
               -> Type -> Type -> (Expr, NameGen)
mkApplyTypeMap ng appToFunc appT funcT =
    let
        (caseName, ng2) = freshName ng
        caseId = Id caseName appT

        (lamName, ng3) = freshName ng2
        lamId = Id lamName appT

        c = Case (Var lamId) caseId $ map (mkApplyTypeMap' appT funcT) appToFunc
    in
    (Lam lamId c, ng3)

unrollNamedTyForAll :: Type -> ([Id], Type)
unrollNamedTyForAll (TyForAll (NamedTyBndr i) ty) =
  let (is, ty') = unrollNamedTyForAll ty in (i:is, ty')
unrollNamedTyForAll ty = ([], ty)

traceTyMap :: Name -> M.Map Name Type -> Maybe Type
traceTyMap name tymap = case M.lookup name tymap of
  Nothing -> Nothing
  Just (TyVar (Id n ty)) -> case traceTyMap n tymap of
    Nothing -> Just $ TyVar (Id n ty)
    Just ty' -> Just ty'
  Just ty -> Just ty

mkApplyTypeMap' :: Type -> Type -> (Name, (Name, Type, M.Map Name Type)) -> Alt
mkApplyTypeMap' appT funcT (app, (func, fty, tymap)) = 
    let
        am = DataAlt (DataCon app appT []) []
        e = Var $ Id func funcT
        tyForAllIds = fst $ unrollNamedTyForAll fty
        e' = foldr (\i ex -> case traceTyMap (idName i) tymap of
                Nothing -> error "mkApplyTypeMap': could not find binding"
                Just ty -> App ex (Type ty))
              e tyForAllIds
    in Alt am e'

-- Returns all functionalizable ADT names (see [1], [2])
functionalizableADTs :: TypeEnv -> [Name]
functionalizableADTs tenv =
    let
        base = baseFuncADTs tenv
        induct = inductFunc base tenv
    in
    nub $ base ++ induct 

-- [1] Get all functionalizable ADTs that directly contain a function parameter
baseFuncADTs :: TypeEnv -> [Name]
baseFuncADTs = baseFuncADTs' . M.toList

baseFuncADTs' :: [(Name, AlgDataTy)] -> [Name]
baseFuncADTs' [] = []
baseFuncADTs' ((n, dc):xs) =
    if any baseFuncDataCon $ dataCon dc 
        then n:baseFuncADTs' xs 
        else baseFuncADTs' xs

baseFuncDataCon :: DataCon -> Bool
baseFuncDataCon (DataCon _ _ ts) = any hasFuncType ts

-- [2] Get all functionalizable ADTs that contain another functionalizable ADT
inductFunc :: [Name] -> TypeEnv -> [Name]
inductFunc ns = inductFunc' ns . M.toList

inductFunc' :: [Name] -> [(Name, AlgDataTy)] -> [Name]
inductFunc' ns nadt = 
    let
        new = nub . map fst $ filter (containsParam ns . snd) nadt
    in
    if length new == length ns then new else ns ++ inductFunc' new nadt

containsParam :: [Name] -> AlgDataTy -> Bool
containsParam ns dc = any (containsParam' ns) $ dataCon dc

containsParam' :: [Name] -> DataCon -> Bool
containsParam' ns (DataCon _ _ ts) = any (containsParam'' ns) ts

containsParam'' :: [Name] -> Type -> Bool
containsParam'' ns (TyConApp n _) = n `elem` ns
containsParam'' _ _ = False


-- We (a) create applied ADTs for all functionalizable ADTs and (b) create
-- functions to convert the applied ADTs to functionalizable ADTs
functionalizableADTsMaps :: [Name] -> TypeEnv -> ExprEnv -> AT.ApplyTypes
                         -> NameGen
                         -> (TypeEnv, ExprEnv, AT.ApplyTypes, NameGen)
functionalizableADTsMaps adts tenv eenv at ng =
    let
        (applyTypes, ng2) = freshSeededNames adts ng
        (applyFuncs, ng3) = freshSeededNames adts ng2

        at2 = foldr 
              (\(t, t', f) ->
                AT.insert (TyConApp t []) t'
                          (Id f (TyFun (TyConApp t' []) (TyConApp t []))))
                at
              $ zip3 adts applyTypes applyFuncs
    in
    functionalizableADTTypes adts tenv eenv at2 ng3

functionalizableADTTypes :: [Name] -> TypeEnv -> ExprEnv -> AT.ApplyTypes -> NameGen -> 
                             (TypeEnv, ExprEnv, AT.ApplyTypes, NameGen)
functionalizableADTTypes [] tenv eenv at ng = (tenv, eenv, at, ng)
functionalizableADTTypes (n:ns) tenv eenv at ng =
    let
        funcADT = M.lookup n tenv

        typeFuncN = AT.lookup (TyConApp n []) at

        (tenv2, eenv2, ng2) =
            case (funcADT, typeFuncN) of
                (Just t, Just (appTypeN, appFuncN)) ->
                  functionalizableADTType appTypeN appFuncN t tenv eenv ng at
                _ -> (tenv, eenv, ng)
    in
    functionalizableADTTypes ns tenv2 eenv2 at ng2

functionalizableADTType :: Name -> Id -> AlgDataTy -> TypeEnv -> ExprEnv
                        -> NameGen -> ApplyTypes -> (TypeEnv, ExprEnv, NameGen)
functionalizableADTType appTypeN (Id appFuncN _) dc tenv eenv ng at =
    let
        -- Create a new Apply Data Type, and put it in the Type Environment 
        (appDCs, ng2) = mkAppliedDCs at ng appTypeN (dataCon dc)
        appAlgDataTy = DataTyCon (bound_names dc) appDCs

        tenv2 = M.insert appTypeN appAlgDataTy tenv

        -- Create a function to map the applied DCs to the functionalizable DCs
        -- and put it in the Expression Environment
        dcAppDc = zip appDCs (dataCon dc)
        (func, ng3) = mkAppliedToFunc at ng2 appTypeN dcAppDc

        eenv2 = E.insert appFuncN func eenv
    in
    (tenv2, eenv2, ng3)

mkAppliedDCs :: ApplyTypes -> NameGen -> Name -> [DataCon] -> ([DataCon], NameGen)
mkAppliedDCs _ ng _ [] = ([], ng)
mkAppliedDCs at ng appTN (DataCon n _ ts:xs) =
    let
        (appN, ng2) = freshSeededName n ng

        appTS = map (\t -> case AT.applyTypeName t at of
                                    Just t' -> TyConApp t' []
                                    Nothing -> t) ts

        appDC = DataCon appN (TyConApp appTN []) appTS

        (en, ng3) = mkAppliedDCs at ng2 appTN xs
    in
    (appDC:en, ng3)

mkAppliedToFunc :: ApplyTypes -> NameGen -> Name -> [(DataCon, DataCon)] -> (Expr, NameGen)
mkAppliedToFunc at ng appTN dcs =
    let
        (lamBindN, ng2) = freshName ng
        lamBindId = Id lamBindN (TyConApp appTN [])

        (caseBindN, ng3) = freshName ng2
        caseBindId = Id caseBindN (TyConApp appTN [])

        (dcs2, ng4) = mkAppliedToAlts at ng3 dcs

        c = Case (Var lamBindId) caseBindId $ dcs2
    in
    (Lam lamBindId c, ng4)

mkAppliedToAlts :: ApplyTypes -> NameGen -> [(DataCon, DataCon)] -> ([Alt], NameGen)
mkAppliedToAlts _ ng [] = ([], ng)
mkAppliedToAlts at ng ((appDC@(DataCon _ _ appTs), funcDC@(DataCon _ _ funcTs)):xs) =
    let
        (paramNames, ng2) = freshNames (length appTs) ng
        paramIds = map (uncurry Id) $ zip paramNames appTs

        am = DataAlt appDC paramIds

        mappedIds = map (uncurry (mkAppliedToAlts' at)) $ zip funcTs paramIds

        dcExpr = foldl' (App) (Data funcDC) mappedIds

        (en, ng3) = mkAppliedToAlts at ng2 xs
    in
    (Alt am dcExpr:en, ng3)

mkAppliedToAlts' :: ApplyTypes -> Type -> Id -> Expr
mkAppliedToAlts' at t i =
    case AT.applyTypeFunc t at of
        Just f -> App (Var f) (Var i)
        Nothing -> Var i
