{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Solver.Simplifier ( Simplifier (..)
                            , IdSimplifier (..)
                            , ADTSimplifier (..)
                            , CombineSimplifiers (..)
                            , EliminateAssumePCs (..)) where

import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import Data.Maybe
import Data.List
import Data.Tuple
import qualified Data.Map as M

import qualified Data.HashSet as HS

class Simplifier simplifier where
    -- | Simplifies a PC, by converting it to a form that is easier for the Solver's to handle
    simplifyPC :: forall t . simplifier -> State t -> PathCond -> (State t, [PathCond])

    {-# INLINE simplifyPCs #-}
    simplifyPCs :: forall t. simplifier -> State t -> PathCond -> PathConds -> PathConds
    simplifyPCs _ _ _ = id

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification :: forall t . simplifier -> State t -> Bindings -> Model -> Model

-- | A simplifier that does no simplification
data IdSimplifier = IdSimplifier

instance Simplifier IdSimplifier where
    simplifyPC _ s pc = (s, [pc])
    reverseSimplification _ _ _ m = m

data CombineSimplifiers a b = a :<< b

instance (Simplifier a, Simplifier b) => Simplifier (CombineSimplifiers a b) where
    simplifyPC (a :<< b) s pc =
        let
            (s', pcs) = simplifyPC b s pc
            (s'', pcs') = mapAccumL (simplifyPC a) s' pcs
        in
        (s'', concat pcs')

    simplifyPCs (a :<< b) s pc pcs = simplifyPCs a s pc $ simplifyPCs b s pc pcs

    reverseSimplification (a :<< b) s binds m = reverseSimplification a s binds $ reverseSimplification b s binds m

-- | A simplifier that converts any ConsConds to ExtConds by mapping the Data Constructor to an Integer
data ADTSimplifier = ADTSimplifier ArbValueFunc

instance Simplifier ADTSimplifier where
    simplifyPC = toNum
    reverseSimplification = fromNum

toNum :: ADTSimplifier -> State t -> PathCond -> (State t, [PathCond])
toNum _ s@(State {adt_int_maps = adtIntMaps
                      , simplified = smplfd
                      , known_values = kv
                      , type_env = tenv}) p
    | p' <- unsafeElimCast p
    , (ConsCond (DataCon dcN _) (Var (Id n t)) bool) <- p' =
        let ogTyp = fromJust . pcVarType $ p
            -- Store type it is cast to (if any), else original type
            isMember = M.member n smplfd
            pcCastTyp = fromJust . pcVarType $ p'
            smplfd' = M.insert n (ogTyp, pcCastTyp) smplfd

            -- Convert `dc` to an Int by looking it up in the respective `dcNumMap`. If not in `dcNumMap`, lookup the corresponding AlgDataTy
            -- , establish a mapping between its DataCons and Ints, and add to `adtTIntMaps`, before returning the respective Int.
            (adtIntMaps'', maybeNum) = case (M.lookup t adtIntMaps) of
                Just dcNumMap -> (adtIntMaps, lookupInt dcN dcNumMap)
                Nothing ->
                    let maybeDCNumMap = mkDCNumMap tenv t
                        num = maybe Nothing (lookupInt dcN) maybeDCNumMap
                        adtIntMaps' = maybe adtIntMaps (insertFlipped t adtIntMaps) maybeDCNumMap
                    in (adtIntMaps', num)
        in case maybeNum of
            Just num ->
                let numericalPC = ExtCond (mkEqIntExpr kv (Var (Id n TyLitInt)) (toInteger num)) bool
                -- Add constraint representing upper and lower bound values for Id in PathCond, depending on the range for its type
                    numBoundPC = case isMember of
                        True -> [] -- Name was already part of map, which means PC representing bounds must have been added already
                        False -> (constrainDCVals kv adtIntMaps'') <$> [(t, Id n TyLitInt)] -- Keep same name to map back to old Id if needed
                in (s {adt_int_maps = adtIntMaps'', simplified = smplfd'}, numericalPC:numBoundPC)
            Nothing -> error $ "Could not simplify ConsCond. " ++ (show p)
    | otherwise = (s, [p])

fromNum :: ADTSimplifier -> State t -> Bindings -> Model -> Model
fromNum (ADTSimplifier avf) (State {adt_int_maps = adtIntMaps
                       , simplified = smplfd
                       , expr_env = eenv
                       , type_env = tenv}) b m = M.mapWithKey (fromNum' eenv tenv adtIntMaps smplfd avf b) m

fromNum' :: E.ExprEnv -> TypeEnv -> ADTIntMaps -> M.Map Name (Type, Type) -> ArbValueFunc -> Bindings -> Name -> Expr -> Expr
fromNum' eenv tenv adtIntMaps smplfd avf b n val
    | Just (t, tCast) <- M.lookup n smplfd -- Tuple representing (original type, type it was cast to)
    , isADT tCast = -- `n` is not of a primitive type, need to map back to DataCon
        let num = case val of
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

            (_, vs) = mapAccumL (\av_ (n', t') ->
                    case E.lookup n' eenv of
                        Just e -> (av_, e)
                        Nothing -> swap $ avf t' tenv av_) (arb_value_gen b) $ zip ns ts''

            dc'' = mkApp $ dc' : map Type ts2 ++ vs
        in liftCasts dc''
    | otherwise = val -- Either primitive value, arbitrary generated value, or value from ExprEnv. Keep current value

-- Lookup ADT and establish mapping between Data Constructors of an ADT and Integers
mkDCNumMap :: TypeEnv -> Type -> Maybe DCNum
mkDCNumMap tenv t =
    let maybeAdt = case getCastedAlgDataTy t tenv of
            Just (adt, _) -> Just adt
            Nothing -> Nothing
    in maybe Nothing mkDCNumMap' maybeAdt

mkDCNumMap' :: AlgDataTy -> Maybe DCNum
mkDCNumMap' (DataTyCon { data_cons = dcs }) =
    let (num, pairs) = mapAccumR (\count dc -> (count + 1, (count, dc))) 0 dcs
        dc2IntPairs = (\(dc, count) -> (dcName dc, count)) <$> swap <$> pairs
    in Just $ DCNum {upperB = num - 1, dc2Int = M.fromList dc2IntPairs, int2Dc = M.fromList pairs}
mkDCNumMap' _ = Nothing

insertFlipped :: Ord a => a -> M.Map a b -> b -> M.Map a b
insertFlipped k m val = M.insert k val m

-- Given an Id with type `t` whose Data Constructors are mapped to [lower, upper], constrain Id to
-- lower <= Id <= upper
constrainDCVals :: KnownValues -> M.Map Type DCNum -> (Type, Id) -> PathCond
constrainDCVals kv m (t, new) =
    let lower = 0
        dcNumMap = fromJust $ M.lookup t m
        upper = upperB dcNumMap
    in ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var new) lower) (mkLeIntExpr kv (Var new) upper)) True

--- Misc Helper Functions ---

pcVarType :: PathCond -> Maybe Type
pcVarType (AltCond _ (Cast (Var (Id _ t)) _) _) = Just t
pcVarType (ConsCond _ (Cast (Var (Id _ t)) _) _) = Just t
pcVarType (AltCond _ (Var (Id _ t)) _) = Just t
pcVarType (ConsCond _ (Var (Id _ t)) _) = Just t
pcVarType _ = Nothing

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

-- Eliminates AssumePC's when the Id is set
data EliminateAssumePCs = EliminateAssumePCs

instance Simplifier EliminateAssumePCs where
    -- | Simplifies a PC, by converting it to a form that is easier for the Solver's to handle
    simplifyPC _ s pc = (s, [pc])

    simplifyPCs _ _ (AltCond (LitInt n) (Var i) True) pcs =
        PC.alterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ (ExtCond (App (App (Prim Eq _) x) y) True) pcs
        | Var i <- x
        , Lit (LitInt n) <- y = PC.alterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ (ExtCond (App (App (Prim Eq _) x) y) True) pcs
        | Var i <- y
        , Lit (LitInt n) <- x = PC.alterHashed (simpAssumePC i n) pcs
    simplifyPCs _ _ _ pcs = pcs

    -- | Reverses the affect of simplification in the model, if needed.
    reverseSimplification _ _ _ = id

simpAssumePC :: Id -> Integer -> PC.HashedPathCond -> Maybe PC.HashedPathCond
simpAssumePC i n exc
    | ExtCond (App (App (Prim Implies _) x) y) True <- PC.unhashedPC exc =
        case x of
            (App (App (Prim Eq _) e1) e2)
                | Lit (LitInt n') <- e1
                , Var i' <- e2 -> simpAssumePC' i n i' n' (PC.hashedPC $ ExtCond y True)
                | Lit (LitInt n') <- e2
                , Var i' <- e1 -> simpAssumePC' i n i' n' (PC.hashedPC $ ExtCond y True)
            _ -> Just exc
simpAssumePC i n p
    | AssumePC i' n' pc <- PC.unhashedPC p = simpAssumePC' i n i' n' pc
simpAssumePC _ _ pc = Just pc

simpAssumePC' :: Id -> Integer -> Id -> Integer -> PC.HashedPathCond -> Maybe PC.HashedPathCond
simpAssumePC' i n i' n' pc
    | i == i' && n == n' = Just pc
    | i == i' && n /= n' = Nothing
    | otherwise = fmap (PC.hashedAssumePC i' n') $ simpAssumePC i n pc