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

import G2.Internals.Initialization.Types
import G2.Internals.Language hiding (State (..))
import qualified G2.Internals.Language.ApplyTypes as AT
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Monad

import Data.List
import qualified Data.Map as M

functionalize :: [Type] -> [Name] -> SimpleStateM (FuncInterps, AT.ApplyTypes)
functionalize ts tgtNames = do
    -- Get names for all need apply type
    eenv <- exprEnv
    tenv <- typeEnv

    let types = filter isTyFun ts ++ (nubBy (.::.) $ argTypesTEnv tenv ++ E.higherOrderExprs eenv)
    
    appT <- applyTypeNames types


    -- Update the expression and type environments with apply types
    (fi, at) <- mkApplyFuncAndTypes appT tgtNames

    return (fi, at)

-- creates ApplyType names for the given types
applyTypeNames :: [Type] -> SimpleStateM [(Type, Name)]
applyTypeNames ts = do
        applyNames <- freshSeededStringsN (replicate (length ts) "applyTy")
        return $ zip ts applyNames

-- Updates the ExprEnv and TypeEnv with ApplyTypes and Apply Functions
-- creates FuncInterps and ApplyTypes tables
mkApplyFuncAndTypes :: [(Type, Name)] -> [Name] ->
                       SimpleStateM (FuncInterps, AT.ApplyTypes)
mkApplyFuncAndTypes tyn tgtNames = do
    eenv' <- return . E.filterWithKey (\n _ -> n `elem` tgtNames) =<< exprEnv

    -- This just gets passed around unmodified in mkApplyFuncTypes'
    -- but precomputing is faster
    let funcT = M.toList $ E.map' typeOf eenv'

    mkApplyFuncAndTypes' tyn funcT (FuncInterps M.empty) (AT.empty)

mkApplyFuncAndTypes' :: [(Type, Name)]
                     -> [(Name, Type)] -> FuncInterps -> AT.ApplyTypes
                     -> SimpleStateM (FuncInterps, AT.ApplyTypes)
mkApplyFuncAndTypes' [] _ fi at = return (fi, at)
mkApplyFuncAndTypes' ((t, n):xs) funcT (FuncInterps fi) at = do
    let funcFolds = foldr (\(n', t') accs ->
                            case specializes M.empty t t' of
                              (True, m) -> (n', t', m) : accs
                              (False, _) -> accs)
                          [] funcT

        funcs = map (\(n', _, _) -> n') funcFolds

    -- Update type environment
    applyCons <- freshSeededNamesN funcs
    
    let dcs = map (\dcn -> DataCon dcn (TyConApp n []) []) applyCons
        adt = DataTyCon [] dcs
    insertT n adt

        -- Update Func Interps
    let applyToFunc = zip applyCons (zip funcs (repeat StdInterp))
        fi' = foldr (uncurry M.insert) fi applyToFunc

    -- ApplyFunc Name
    applyFuncN <- freshSeededStringN "applyFunc"

    -- Update Apply Types
    let applyFunc = Id applyFuncN (TyFun (TyConApp n []) t)
        at2 = AT.insert t n applyFunc at

    -- Update expression enviroment
    expr <- mkApplyTypeMap (zip applyCons funcFolds) (TyConApp n []) t

    insertE applyFuncN expr

    mkApplyFuncAndTypes' xs funcT (FuncInterps fi') at2

-- Makes a function to map the apply types to the cooresponding Apply Functions
mkApplyTypeMap :: [(Name, (Name, Type, M.Map Name Type))] -> Type -> Type -> SimpleStateM Expr
mkApplyTypeMap appToFunc appT funcT = do
    caseId <- freshIdN appT
    lamId <- freshIdN appT

    let c = Case (Var lamId) caseId $ map (mkApplyTypeMap' appT funcT) appToFunc

    return $ Lam lamId c

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
    in
    Alt am e'

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
functionalizableADTsMaps :: [Name] -> AT.ApplyTypes -> SimpleStateM AT.ApplyTypes
functionalizableADTsMaps adts at = do
    applyTypes <- freshSeededNamesN adts
    applyFuncs <- freshSeededNamesN adts

    let at2 = foldr 
              (\(t, t', f) ->
                AT.insert (TyConApp t []) t'
                          (Id f (TyFun (TyConApp t' []) (TyConApp t []))))
                at
              $ zip3 adts applyTypes applyFuncs
    
    functionalizableADTTypes adts at2

functionalizableADTTypes :: [Name] -> AT.ApplyTypes -> SimpleStateM AT.ApplyTypes
functionalizableADTTypes []  at = return at
functionalizableADTTypes (n:ns) at = do
    funcADT <- lookupT n

    let typeFuncN = AT.lookup (TyConApp n []) at

    case (funcADT, typeFuncN) of
        (Just t, Just (appTypeN, appFuncN)) ->
            functionalizableADTType appTypeN appFuncN t at
        _ -> return ()

    functionalizableADTTypes ns at

functionalizableADTType :: Name -> Id -> AlgDataTy -> ApplyTypes -> SimpleStateM ()
functionalizableADTType appTypeN (Id appFuncN _) dc at = do
    -- Create a new Apply Data Type, and put it in the Type Environment
    appDCs <- mkAppliedDCs at appTypeN (dataCon dc)
    
    let appAlgDataTy = DataTyCon (bound_names dc) appDCs

    insertT appTypeN appAlgDataTy

    -- Create a function to map the applied DCs to the functionalizable DCs
    -- and put it in the Expression Environment
    let dcAppDc = zip appDCs (dataCon dc)

    func <- mkAppliedToFunc at appTypeN dcAppDc

    insertE appFuncN func

    return ()

mkAppliedDCs :: ApplyTypes -> Name -> [DataCon] -> SimpleStateM [DataCon]
mkAppliedDCs _ _ [] = return []
mkAppliedDCs at appTN (DataCon n _ ts:xs) = do
    appN <- freshSeededNameN n

    let appTS = map (\t -> case AT.applyTypeName t at of
                                Just t' -> TyConApp t' []
                                Nothing -> t) ts

        appDC = DataCon appN (TyConApp appTN []) appTS

    en <- mkAppliedDCs at appTN xs
    
    return $ appDC:en

mkAppliedToFunc :: ApplyTypes -> Name -> [(DataCon, DataCon)] -> SimpleStateM Expr
mkAppliedToFunc at appTN dcs = do
    lamBindId <- freshIdN (TyConApp appTN [])

    caseBindId <- freshIdN (TyConApp appTN [])

    dcs2<- mkAppliedToAlts at dcs

    let c = Case (Var lamBindId) caseBindId $ dcs2

    return $ Lam lamBindId c

mkAppliedToAlts :: ApplyTypes -> [(DataCon, DataCon)] -> SimpleStateM [Alt]
mkAppliedToAlts _ [] = return []
mkAppliedToAlts at ((appDC@(DataCon _ _ appTs), funcDC@(DataCon _ _ funcTs)):xs) = do
    paramIds <- freshIdsN appTs

    let am = DataAlt appDC paramIds
        mappedIds = map (uncurry (mkAppliedToAlts' at)) $ zip funcTs paramIds
        dcExpr = foldl' (App) (Data funcDC) mappedIds

    en <- mkAppliedToAlts at xs
    
    return $ Alt am dcExpr:en

mkAppliedToAlts' :: ApplyTypes -> Type -> Id -> Expr
mkAppliedToAlts' at t i =
    case AT.applyTypeFunc t at of
        Just f -> App (Var f) (Var i)
        Nothing -> Var i
