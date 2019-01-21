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

module G2.Initialization.Functionalizer (functionalize) where

import G2.Language hiding (State (..))
import qualified G2.Language.ApplyTypes as AT
import qualified G2.Language.ExprEnv as E
import G2.Language.Monad

import Data.List
import qualified Data.Map as M

functionalize :: ExState s m => [Type] -> [Name] -> m (FuncInterps, AT.ApplyTypes)
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
applyTypeNames :: ExState s m => [Type] -> m [(Type, Name)]
applyTypeNames ts = do
        applyNames <- freshSeededStringsN (replicate (length ts) "applyTy")
        return $ zip ts applyNames

-- Updates the ExprEnv and TypeEnv with ApplyTypes and Apply Functions
-- creates FuncInterps and ApplyTypes tables
mkApplyFuncAndTypes :: ExState s m => [(Type, Name)] -> [Name] ->
                       m (FuncInterps, AT.ApplyTypes)
mkApplyFuncAndTypes tyn tgtNames = do
    eenv' <- return . E.filterWithKey (\n _ -> n `elem` tgtNames) =<< exprEnv

    -- This just gets passed around unmodified in mkApplyFuncTypes'
    -- but precomputing is faster
    let funcT = M.toList $ E.map' typeOf eenv'

    mkApplyFuncAndTypes' tyn funcT (FuncInterps M.empty) (AT.empty)

mkApplyFuncAndTypes' :: ExState s m => [(Type, Name)]
                     -> [(Name, Type)] -> FuncInterps -> AT.ApplyTypes
                     -> m (FuncInterps, AT.ApplyTypes)
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
    
    let dcs = map (\dcn -> DataCon dcn (TyCon n TYPE)) applyCons
        adt = DataTyCon [] dcs
    insertT n adt

        -- Update Func Interps
    let applyToFunc = zip applyCons (zip funcs (repeat StdInterp))
        fi' = foldr (uncurry M.insert) fi applyToFunc

    -- ApplyFunc Name
    applyFuncN <- freshSeededStringN "applyFunc"

    -- Update Apply Types
    let applyFunc = Id applyFuncN (TyFun (TyCon n TYPE) t)
        at2 = AT.insert t n applyFunc at

    -- Update expression enviroment
    expr <- mkApplyTypeMap (zip applyCons funcFolds) (TyCon n TYPE) t

    insertE applyFuncN expr

    mkApplyFuncAndTypes' xs funcT (FuncInterps fi') at2

-- Makes a function to map the apply types to the cooresponding Apply Functions
mkApplyTypeMap :: ExState s m => [(Name, (Name, Type, M.Map Name Type))] -> Type -> Type -> m Expr
mkApplyTypeMap appToFunc appT funcT = do
    caseId <- freshIdN appT
    lamId <- freshIdN appT

    let c = Case (Var lamId) caseId $ map (mkApplyTypeMap' appT funcT) appToFunc

    return $ Lam TermL lamId c

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
        am = DataAlt (DataCon app appT) []
        e = Var $ Id func funcT
        tyForAllIds = fst $ unrollNamedTyForAll fty
        e' = foldr (\i ex -> case traceTyMap (idName i) tymap of
                Nothing -> error "mkApplyTypeMap': could not find binding"
                Just ty -> App ex (Type ty))
              e tyForAllIds
    in
    Alt am e'
