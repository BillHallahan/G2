{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Solver.ADTSolver ( ADTSolver (..)
                           , adtSolverFinite
                           , adtSolverInfinite
                           , checkConsistency
                           , findConsistent) where

import G2.Language.ArbValueGen
import G2.Language.Casts
import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.PathConds hiding (map, filter, null)
import qualified G2.Language.PathConds as PC
import G2.Language.Typing
import G2.Solver.Solver

import Data.List
import qualified Data.HashMap.Lazy as HM
import Data.Maybe
import Prelude hiding (null)
import qualified Prelude as Pre
import Data.Tuple

data ADTSolver = ADTSolver ArbValueFunc

adtSolverFinite :: ADTSolver
adtSolverFinite = ADTSolver arbValue

adtSolverInfinite :: ADTSolver
adtSolverInfinite = ADTSolver arbValueInfinite

instance Solver ADTSolver where
    check _ s = return .checkConsistency (known_values s) (expr_env s) (type_env s)
    solve (ADTSolver avf) s b is = solveADTs avf s b (nub is) 

-- | Attempts to detemine if the given PathConds are consistent.
-- Returns Just True if they are, Just False if they are not,
-- and Nothing if it can't decide.
checkConsistency :: KnownValues -> ExprEnv -> TypeEnv -> PathConds -> Result
checkConsistency kv eenv tenv pc =
    maybe (Unknown "Non-ADT path constraints")
          (\me -> if not (Pre.null me) then SAT else UNSAT)
          $ findConsistent kv eenv tenv pc

-- | Attempts to find expressions (Data d) or (Coercion (Data d), (t1 :~ t2)) consistent with the given path
-- constraints.  Returns Just [...] if it can determine [...] are consistent.
-- Just [] means there are no consistent Expr.  Nothing nmeans it could not be
-- determined if there were any consistent data constructors.
-- In practice, the result should always be Just [...] if all the path conds
-- are about ADTs.
findConsistent :: KnownValues -> ExprEnv -> TypeEnv -> PathConds -> Maybe [Expr]
findConsistent kv eenv tenv = fmap fst . findConsistent' kv eenv tenv

head' :: [a] -> Maybe a
head' (x:_) = Just x
head' _ = Nothing

findConsistent' :: KnownValues -> ExprEnv -> TypeEnv -> PathConds -> Maybe ([Expr], [(Id, Type)])
findConsistent' kv eenv tenv pc =
    let
        pc' = unsafeElimCast $ toList pc

        -- Adding Coercions
        pcNT = fmap (pcInCastType tenv) . head' $ toList pc
        cons = findConsistent'' kv tenv eenv pc'
    in
    case cons of
        Just (cons', bi) ->
            let
                cons'' = simplifyCasts . map (castReturnType $ fromJust pcNT) $ cons'
            in
            -- We can't use the ADT solver when we have a Boolean, because the RHS of the
            -- DataAlt might be a primitive.
            if any isExtCond pc' || pcNT == Just (tyBool kv) then Nothing else Just (cons'', bi)
        Nothing -> Nothing

findConsistent'' :: KnownValues -> TypeEnv -> ExprEnv -> [PathCond] -> Maybe ([Expr], [(Id, Type)])
findConsistent'' kv tenv eenv pc =
    let
        is = nub . map (\(Id n t') -> Id n (typeStripCastType tenv t')) $ concatMap varIdsInPC pc

        t = pcVarType tenv pc
        cons = maybe Nothing (flip getCastedAlgDataTy tenv) t
    
    in
    case (cons, is) of 
        (Just (DataTyCon _ dc, bi), [i]) ->
            let
                dc' = case E.lookup (idName i) eenv of
                        Just e
                            | Data spec_dc:_ <- unApp e -> [spec_dc]
                        _ -> dc
                

                cons' = fmap (map Data) $ findConsistent''' dc' pc
            in
            maybe Nothing (Just . (, bi)) cons'
        _ -> Nothing

findConsistent''' :: [DataCon] -> [PathCond] -> Maybe [DataCon]
findConsistent''' dcs ((ConsCond dc _ True):pc) =
    findConsistent''' (filter ((==) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs ((ConsCond  dc _ False):pc) =
    findConsistent''' (filter ((/=) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs [] = Just dcs
findConsistent''' _ _ = Nothing

solveADTs :: ArbValueFunc -> State t -> Bindings -> [Id] -> PathConds -> IO (Result, Maybe Model)
solveADTs avf s@(State { expr_env = eenv, model = m }) b [Id n t] pc
    | not $ E.isSymbolic n eenv
    , Just e <- E.lookup n eenv = return (SAT, Just . liftCasts $ HM.insert n e m )
    -- We can't use the ADT solver when we have a Boolean, because the RHS of the
    -- DataAlt might be a primitive.
    | TyCon tn k <- tyAppCenter t
    , ts <- tyAppArgs t
    , t /= tyBool (known_values s)  =
    do
        let (r, s', _) = addADTs avf n tn ts k s b pc

        case r of
            SAT -> return (r, Just . liftCasts $ model s')
            r' -> return (r', Nothing)
solveADTs _ _ _ _ _ = return (Unknown "Unhandled path constraints in ADTSolver", Nothing)

-- | Determines an ADT based on the path conds.  The path conds form a witness.
-- In particular, refer to findConsistent in Solver/ADTSolver.hs
addADTs :: ArbValueFunc -> Name -> Name -> [Type] -> Kind -> State t -> Bindings -> PathConds -> (Result, State t, Bindings)
addADTs avf n tn ts k s b pc
    | PC.null pc =
        let
            (bse, av) = avf (mkTyApp (TyCon tn k:ts)) (type_env s) (arb_value_gen b)
            m' = HM.singleton n bse
        in
        (SAT, (s {model = HM.union m' (model s)}), (b {arb_value_gen = av}))
    | Just (dcs@(fdc:_), bi) <- findConsistent' (known_values s) (expr_env s) (type_env s) pc =
    let        
        eenv = expr_env s
        ts2 = map snd bi
        -- We map names over the arguments of a DataCon, to make sure we have the correct
        -- number of undefined's.
        ts'' = case exprInCasts fdc of
            Data (DataCon _ ts') -> anonArgumentTypes $ PresType ts'
            _ -> [] -- [Name "b" Nothing 0 Nothing]

        (ns, _) = childrenNames n (map (const $ Name "a" Nothing 0 Nothing) ts'') (name_gen b)

        (av, vs) = mapAccumL (\av_ (n', t') -> 
                case E.lookup n' eenv of
                    Just e -> (av_, e)
                    Nothing -> swap $ avf t' (type_env s) av_) (arb_value_gen b) $ zip ns ts''
        
        dc = mkApp $ fdc:map Type ts2 ++ vs

        m = HM.insert n dc (model s)
    in
    case not . Pre.null $ dcs of
        True -> (SAT, s { model = HM.union m (model s) }, b { arb_value_gen = av })
        False -> (UNSAT, s, b)
    | otherwise = (UNSAT, s, b)

-- Various helper functions

isExtCond :: PathCond -> Bool
isExtCond (ExtCond _ _) = True
isExtCond _ = False

pcVarType :: TypeEnv -> [PathCond] -> Maybe Type
pcVarType tenv (AltCond _ (Var (Id _ t)) _:pc) = pcVarType' t tenv pc
pcVarType tenv (ConsCond _ (Var (Id _ t)) _:pc) = pcVarType' t tenv pc
pcVarType _ _ = Nothing

pcVarType' :: Type -> TypeEnv -> [PathCond] -> Maybe Type
pcVarType' t tenv (AltCond _ (Var (Id _ t')) _:pc) =
    if t == t' then pcVarType' t tenv pc else Nothing
pcVarType' t tenv (ConsCond _ (Var (Id _ t')) _:pc) =
    if t == t' then pcVarType' t tenv pc else Nothing
pcVarType' n _ [] = Just n
pcVarType' _ _ _ = Nothing

pcInCastType :: TypeEnv -> PathCond -> Type
pcInCastType _ (AltCond _ e _) = typeInCasts e
pcInCastType _ (ExtCond e _) = typeInCasts e
pcInCastType _ (ConsCond _ e _) = typeInCasts e

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
