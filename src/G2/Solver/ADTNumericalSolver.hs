{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.ADTNumericalSolver ( ADTNumericalSolver (..)
                                    , adtNumericalSolFinite
                                    , adtNumericalSolInfinite) where

import G2.Language.ArbValueGen
import G2.Language.Casts
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import qualified G2.Language.PathConds as PC
import G2.Language.Typing
import G2.Solver.Solver

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Tuple

-- | Converts constraints about ADTs to numerical constraints before sending them to other solvers
data ADTNumericalSolver a = ADTNumericalSolver ArbValueFunc a

adtNumericalSolFinite :: a -> ADTNumericalSolver a
adtNumericalSolFinite = ADTNumericalSolver arbValue

adtNumericalSolInfinite :: a -> ADTNumericalSolver a
adtNumericalSolInfinite = ADTNumericalSolver arbValueInfinite

instance Solver solver => Solver (ADTNumericalSolver solver) where
    check (ADTNumericalSolver _ sol) s pc = return . fst =<< checkConsistency (Tr sol) s pc
    solve (ADTNumericalSolver avf sol) s b is pc =
        return . (\(r, m, _) -> (r, m)) =<< solve' avf (Tr sol) s b is pc
    close (ADTNumericalSolver _ s) = close s

instance TrSolver solver => TrSolver (ADTNumericalSolver solver) where
    checkTr (ADTNumericalSolver avf sol) s pc = do
        (r, sol') <- checkConsistency sol s pc
        return (r, ADTNumericalSolver avf sol')
    solveTr (ADTNumericalSolver avf sol) s b is pc = do
        (r, m, sol') <- solve' avf sol s b is pc
        return (r, m, ADTNumericalSolver avf sol')
    closeTr (ADTNumericalSolver _ s) = closeTr s

checkConsistency :: TrSolver a => a -> State t -> PathConds -> IO (Result, a)
checkConsistency solver s@(State {known_values = kv}) pc
    | PC.null pc = return (SAT, solver)
    | otherwise = do
        let pc' = unsafeElimCast $ filter (not . PC.isPCExists) $ PC.toList pc
            -- Convert any ConsConds to ExtConds by mapping the respective DataCon to an Int
            -- Also lookup any constraints from the expr_env, map to Ints and add
            (pc'', _) = toNumericalPCs s pc'
        checkTr solver s (PC.fromList kv pc'')

solve' :: TrSolver a => ArbValueFunc -> a -> State t -> Bindings -> [Id] -> PathConds -> IO (Result, Maybe Model, a)
solve' avf sol s@(State {known_values = kv}) b is pc = do
    let pc' = unsafeElimCast $ filter (not . PC.isPCExists) $ PC.toList pc
        -- Store type it is cast to (if any), else original type
        pcCastTyp = M.fromList $ mapMaybe pcVarNameType pc'
        -- Convert any ConsConds to ExtConds by mapping the respective DataCon to an Int
        -- Also lookup any constraints from the expr_env and add them
        (pc'', adtIntMaps) = toNumericalPCs s pc'
        -- Use other solvers to solve for Ids that have primitive types and new Ids added by converting ConsCond-s to ExtConds
        pcIds = (concatMap PC.varIdsInPC pc'') ++ (filter (not . isADT . (\(Id _ t) -> t)) is)
        is' = nub is
    rm <- solveTr sol s b pcIds (PC.fromList kv pc'')
    case rm of
        (SAT, Just m, sol') ->
            let (_, m') = foldr (solve'' avf s pcCastTyp adtIntMaps) (b,m) is'
            in return (SAT, Just $ liftCasts m', sol')
        _ -> return rm

solve'' :: ArbValueFunc -> State t -> (M.Map Name Type) -> (M.Map Type DCNum) -> Id -> (Bindings, Model) -> (Bindings, Model)
solve'' avf (State {expr_env = eenv, type_env = tenv}) pcCastTyp adtIntMaps (Id n t) (b, m)
    | M.member n m 
    , (Just tCast) <- M.lookup n pcCastTyp -- Type it was cast to
    , isADT tCast = -- `n` is not of a primitive type, need to map back to DataCon
        let val = fromJust $ M.lookup n m
            num = case val of
                (Lit (LitInt x)) -> x
                _ -> error "Model should only return LitInts for non-primitive type"
            dcNumMap = fromJust $ M.lookup tCast adtIntMaps
            dc = Data $ fromJust $ lookupDC num dcNumMap

            dc' = if tCast /= t
                then simplifyCasts . (castReturnType t) $ dc -- Apply the cast type back
                else dc
            (_, bi) = fromJust $ getCastedAlgDataTy tCast tenv
            ts2 = map snd bi
            -- We map names over the arguments of a DataCon, to make sure we have the correct number of undefined's.
            ts'' = case exprInCasts dc' of
                Data (DataCon _ ts') -> anonArgumentTypes $ PresType ts'
                _ -> [] -- [Name "b" Nothing 0 Nothing]

            (ns, _) = childrenNames n (map (const $ Name "a" Nothing 0 Nothing) ts'') (name_gen b)

            (av, vs) = mapAccumL (\av_ (n', t') ->
                    case E.lookup n' eenv of
                        Just e -> (av_, e)
                        Nothing -> swap $ avf t' tenv av_) (arb_value_gen b) $ zip ns ts''
            
            dc'' = mkApp $ dc':map Type ts2 ++ vs
        in (b {arb_value_gen = av}, M.insert n dc'' m)
    | M.member n m = (b, m) -- Primitive value, keep the current value in model
    | not $ E.isSymbolic n eenv
    , Just e <- E.lookup n eenv = (b, M.insert n e m)
    | TyCon tn k <- tyAppCenter t -- Generate arbitrary value
    , ts <- tyAppArgs t =
        let
            (bse, av) = avf (mkTyApp (TyCon tn k:ts)) tenv (arb_value_gen b)
            m' = M.singleton n bse
        in (b {arb_value_gen = av}, M.union m' m)
    | otherwise = error $ "Unsolved name: " ++ show n

toNumericalPCs :: State t -> [PathCond] -> ([PathCond], M.Map Type DCNum)
toNumericalPCs s@(State {known_values = kv, type_env = tenv, expr_env = eenv}) pc =
    let -- `adtIntMaps` can be thought of as a Map between a Type and [(DataCons, Int)] pairings for that type
        adtIntMaps = M.empty
        ((adtIntMaps', extCondIds), pc') = mapAccumR (toExtCond s) (adtIntMaps, []) pc
        -- Add constraints representing upper and lower bound values for each Id in pcIds', depending on the range for its type
        valLims = (constrainDCVals kv adtIntMaps') <$> extCondIds
        -- Add any constraints from expr_env
        eenvVals = mapMaybe (addEEnvVals kv tenv eenv adtIntMaps') extCondIds
    in (eenvVals ++ valLims ++ pc', adtIntMaps')

toExtCond :: State t -> (M.Map Type DCNum, [(Id, Id)]) -> PathCond -> ((M.Map Type DCNum, [(Id, Id)]), PathCond)
toExtCond _ (adtIntMaps, pcIds) p@(AltCond _ _ _) = ((adtIntMaps, pcIds), p)
toExtCond _ (adtIntMaps, pcIds) p@(ExtCond _ _) = ((adtIntMaps, pcIds), p)
toExtCond (State {type_env = tenv, known_values = kv}) (adtIntMaps, pcIds) (ConsCond dc@(DataCon _ _) (Var i@(Id n t)) bool) =
    -- Convert `dc` to an Int by looking it up in `dcIntMap`. If `dc` not in `dcIntMap`, lookup the corresponding AlgDataTy
    -- , establish a mapping between its DataCons and Ints, and add to `adtIntMaps`, before returning the respective Int.
    let (adtIntMaps'', maybeNum) = case (M.lookup t adtIntMaps) of
            Just dcNumMap -> (adtIntMaps, lookupInt dc dcNumMap)
            Nothing ->
                let maybeAdt = case getCastedAlgDataTy t tenv of
                        Just (adt, _) -> Just adt
                        Nothing -> Nothing
                    maybeDcNumMap = maybe Nothing mkDCNumMap maybeAdt
                    num = maybe Nothing (lookupInt dc) maybeDcNumMap
                    adtIntMaps' = maybe adtIntMaps (insertFlipped t adtIntMaps) maybeDcNumMap
                in (adtIntMaps', num)
        i' = Id n TyLitInt -- Keep same name to map back to old Id if needed
        e' = Var i'
    in case maybeNum of
        Just num -> ((adtIntMaps'', (i, i'):pcIds), ExtCond (mkEqIntExpr kv e' (toInteger num)) bool)
        Nothing -> error $ "Could not map DataCon in ConsCond to Int: " ++ (show dc)
toExtCond _ (adtIntMaps, pcIds) p = ((adtIntMaps, pcIds), p)

-- Establish mapping between Data Constructors of an ADT and Integers
mkDCNumMap :: AlgDataTy -> Maybe DCNum
mkDCNumMap (DataTyCon { data_cons = dcs }) =
    let (num, pairings) = mapAccumR (\count dc -> (count + 1, (dc, count))) 0 dcs
    in Just $ DCNum {upperB = num - 1, dc2Int = M.fromList pairings, int2Dc = M.fromList (swap <$> pairings)}
mkDCNumMap _ = Nothing

insertFlipped :: Ord a => a -> M.Map a b -> b -> M.Map a b
insertFlipped k m val = M.insert k val m

-- Given an Id with type `t` whose Data Constructors are mapped to [lower, upper], constrain Id to
-- lower <= Id <= upper
constrainDCVals :: KnownValues -> M.Map Type DCNum -> (Id, Id) -> PathCond
constrainDCVals kv m ((Id _ t), new) =
    let lower = 0
        dcNumMap = fromJust $ M.lookup t m
        upper = upperB dcNumMap
    in ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var new) lower) (mkLeIntExpr kv (Var new) upper)) True

addEEnvVals :: KnownValues -> TypeEnv -> ExprEnv -> M.Map Type DCNum -> (Id, Id) -> Maybe PathCond
addEEnvVals kv tenv eenv adtIntMaps (old, new) =
    let (Id n' t') = (\(Id n t) -> Id n (typeStripCastType tenv t)) old
    in case E.lookup n' eenv of
        Just e
            | Data spec_dc:_ <- unApp e ->
                let dcNumMap = fromJust $ M.lookup t' adtIntMaps
                    num = fromJust $ lookupInt spec_dc dcNumMap
                in Just $ ExtCond (mkEqIntExpr kv (Var new) (toInteger num)) True
        _ -> Nothing

--- Misc Helper Functions ---

pcVarNameType :: PathCond -> Maybe (Name, Type)
pcVarNameType (AltCond _ (Var (Id n t)) _) = Just (n, t)
pcVarNameType (ConsCond _ (Var (Id n t)) _) = Just (n, t)
pcVarNameType _ = Nothing

castReturnType :: Type -> Expr -> Expr
castReturnType t e =
    let
        te = typeOf e
        tr = replaceReturnType te t
    in
    Cast e (te :~ tr)

replaceReturnType :: Type -> Type -> Type
replaceReturnType (TyForAll b t) r = TyForAll b $ replaceReturnType t r
replaceReturnType (TyFun t1 t2@(TyFun _ _)) r = TyFun t1 $ replaceReturnType t2 r
replaceReturnType (TyFun t _) r = TyFun t r
replaceReturnType _ r = r

isADT :: Type -> Bool
isADT t =
    let tCenter = tyAppCenter t
    in case tCenter of
        (TyCon _ _) -> True
        _ -> False
