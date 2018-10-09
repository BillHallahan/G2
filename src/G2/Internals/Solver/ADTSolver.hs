{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module G2.Internals.Solver.ADTSolver ( ADTSolver (..)
                                     , checkConsistency
                                     , findConsistent) where

import G2.Internals.Language.ArbValueGen
import G2.Internals.Language.Casts
import G2.Internals.Language.Expr
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Language.Naming
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.PathConds hiding (map, null)
import qualified G2.Internals.Language.PathConds as PC
import G2.Internals.Language.Typing
import G2.Internals.Solver.Solver

import Data.List
import qualified Data.Map as M
import Data.Maybe
import Prelude hiding (null)
import qualified Prelude as Pre

data ADTSolver = ADTSolver

instance Solver ADTSolver where
    check _ s = return . checkConsistency (known_values s) (type_env s)
    solve _ s is = solveADTs s (nub is)

-- | Attempts to detemine if the given PathConds are consistent.
-- Returns Just True if they are, Just False if they are not,
-- and Nothing if it can't decide.
checkConsistency :: KnownValues -> TypeEnv -> PathConds -> Result
checkConsistency kv tenv pc = maybe 
                                (Unknown "Non-ADT path constraints") 
                                (\me -> if not (Pre.null me) then SAT else UNSAT) 
                                $ findConsistent kv tenv pc

-- | Attempts to find expressions (Data d) or (Coercion (Data d), (t1 :~ t2)) consistent with the given path
-- constraints.  Returns Just [...] if it can determine [...] are consistent.
-- Just [] means there are no consistent Expr.  Nothing nmeans it could not be
-- determined if there were any consistent data constructors.
-- In practice, the result should always be Just [...] if all the path conds
-- are about ADTs.
findConsistent :: KnownValues -> TypeEnv -> PathConds -> Maybe [Expr]
findConsistent kv tenv = fmap fst . findConsistent' kv tenv

head' :: [a] -> Maybe a
head' (x:_) = Just x
head' _ = Nothing

solveADTs :: State t -> [Id] -> PathConds -> IO (Result, Maybe Model)
solveADTs s [Id n t] pc
    -- We can't use the ADT solver when we have a Boolean, because the RHS of the
    -- DataAlt might be a primitive.
    | TyCon tn k <- tyAppCenter t
    , ts <- tyAppArgs t
    , t /= tyBool (known_values s)  =
    do
        let (r, s') = addADTs n tn ts k s pc

        case r of
            SAT -> return (r, Just . liftCasts $ model s')
            r' -> return (r', Nothing)
solveADTs _ _ _ = return (Unknown "Unhandled path constraints in ADTSolver", Nothing)

-- | Determines an ADT based on the path conds.  The path conds form a witness.
-- In particular, refer to findConsistent in Solver/ADTSolver.hs
addADTs :: Name -> Name -> [Type] -> Kind -> State t -> PathConds -> (Result, State t)
addADTs n tn ts k s pc
    | PC.null pc =
        let
            (bse, av) = arbValue (mkTyApp (TyCon tn k:ts)) (type_env s) (arbValueGen s)
            m' = M.singleton n bse
        in
        (SAT, s {model = M.union m' (model s), arbValueGen = av})
    | Just (dcs@(fdc:_), bi) <- findConsistent' (known_values s) (type_env s) pc =
    let        
        eenv = expr_env s
        ts2 = map snd bi
        -- We map names over the arguments of a DataCon, to make sure we have the correct
        -- number of undefined's.
        ts'' = case exprInCasts fdc of
            Data (DataCon _ ts') -> anonArgumentTypes $ PresType ts'
            _ -> [] -- [Name "b" Nothing 0 Nothing]

        (ns, _) = childrenNames n (map (const $ Name "a" Nothing 0 Nothing) ts'') (name_gen s)

        vs = map (\(n', t') -> 
                case E.lookup n' eenv of
                    Just e -> e
                    Nothing -> fst $ arbValue t' (type_env s) (arbValueGen s)) $ zip ns ts''
        
        dc = mkApp $ fdc:map Type ts2 ++ vs

        m = M.insert n dc (model s)
    in
    case not . Pre.null $ dcs of
        True -> (SAT, s {model = M.union m (model s)})
        False -> (UNSAT, s)
    | otherwise = (UNSAT, s)

findConsistent' :: KnownValues -> TypeEnv -> PathConds -> Maybe ([Expr], [(Id, Type)])
findConsistent' kv tenv pc =
    let
        pc' = unsafeElimCast $ toList pc

        -- Adding Coercions
        pcNT = fmap pcInCastType . head' $ toList pc
        cons = findConsistent'' tenv pc'
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

findConsistent'' :: TypeEnv -> [PathCond] -> Maybe ([Expr], [(Id, Type)])
findConsistent'' tenv pc =
    let
        t = pcVarType pc
        cons = maybe Nothing (flip getCastedAlgDataTy tenv) t
    
    in
    case cons of 
        Just (DataTyCon _ dc, bi) ->
            let
                cons' = fmap (map Data) $ findConsistent''' dc pc
            in
            maybe Nothing (Just . (, bi)) cons'
        _ -> Nothing

findConsistent''' :: [DataCon] -> [PathCond] -> Maybe [DataCon]
findConsistent''' dcs ((AltCond (DataAlt dc _) _ True):pc) =
    findConsistent''' (filter ((==) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs ((AltCond (DataAlt dc _) _ False):pc) =
    findConsistent''' (filter ((/=) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs ((ConsCond dc _ True):pc) =
    findConsistent''' (filter ((==) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs ((ConsCond  dc _ False):pc) =
    findConsistent''' (filter ((/=) (dcName dc) . dcName) dcs) pc
findConsistent''' dcs [] = Just dcs
findConsistent''' _ _ = Nothing


-- Various helper functions

isExtCond :: PathCond -> Bool
isExtCond (ExtCond _ _) = True
isExtCond _ = False

pcVarType :: [PathCond] -> Maybe Type
pcVarType (AltCond _ (Var (Id _ t)) _:pc) = pcVarType' t pc
pcVarType (ConsCond _ (Var (Id _ t)) _:pc) = pcVarType' t pc
pcVarType _ = Nothing

pcVarType' :: Type -> [PathCond] -> Maybe Type
pcVarType' t (AltCond _ (Var (Id _ t')) _:pc) =
    if t == t' then pcVarType' t pc else Nothing
pcVarType' t (ConsCond _ (Var (Id _ t')) _:pc) =
    if t == t' then pcVarType' t pc else Nothing
pcVarType' n [] = Just n
pcVarType' _ _ = Nothing

pcInCastType :: PathCond -> Type
pcInCastType (AltCond _ e _) = typeInCasts e
pcInCastType (ExtCond e _) = typeInCasts e
pcInCastType (ConsCond _ e _) = typeInCasts e
pcInCastType (PCExists (Id _ t)) = t

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
