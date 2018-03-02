module G2.Internals.Solver.ADTSolver ( checkConsistency
                                     , findConsistent) where

import G2.Internals.Language.Casts
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.PathConds hiding (map)
import G2.Internals.Language.Typing

import Data.Maybe
import Prelude hiding (null)
import qualified Prelude as Pre

import Debug.Trace

-- | checkConsistency
-- Attempts to detemine if the given PathConds are consistent.
-- Returns Just True if they are, Just False if they are not,
-- and Nothing if it can't decide.
checkConsistency :: KnownValues -> TypeEnv -> PathConds -> Maybe Bool
checkConsistency kv tenv pc = maybe Nothing (Just . not . Pre.null) $ findConsistent kv tenv pc

-- | findConsistent
-- Attempts to find expressions (Data d) or (Coercion (Data d), (t1 :~ t2)) consistent with the given path
-- constraints.  Returns Just [...] if it can determine [...] are consistent.
-- Just [] means there are no consistent Expr.  Nothing nmeans it could not be
-- determined if there were any consistent data constructors.
-- In practice, the result should always be Just [...] if all the path conds
-- are about ADTs.
findConsistent :: KnownValues -> TypeEnv -> PathConds -> Maybe [Expr]
findConsistent kv tenv pc =
    let
        pc' = unsafeElimCast $ toList pc

        -- Adding Coercions
        pcNT = fmap pcInCastType . head' $ toList pc
        cons = findConsistent' tenv pc'

        cons' = fmap (simplifyCasts . map (castReturnType $ fromJust pcNT)) cons 
    in
    -- We can't use the ADT solver when we have a Boolean, because the RHS of the
    -- DataAlt might be a primitive.
    if any isExtCond pc' || pcNT == Just (tyBool kv) then Nothing else cons'

head' :: [a] -> Maybe a
head' (x:_) = Just x
head' _ = Nothing

findConsistent' :: TypeEnv -> [PathCond] -> Maybe [Expr]
findConsistent' tenv pc =
    let
        n = pcVarType pc
        adt = maybe Nothing (\n' -> getCastedAlgDataTy n' tenv) n
    in
    maybe Nothing (\(DataTyCon _ dc) -> fmap (map Data) $ findConsistent'' dc pc) adt

findConsistent'' :: [DataCon] -> [PathCond] -> Maybe [DataCon]
findConsistent'' dcs ((AltCond (DataAlt dc _) _ True):pc) =
    findConsistent'' (filter ((==) (dcName dc) . dcName) dcs) pc
findConsistent'' dcs ((AltCond (DataAlt dc _) _ False):pc) =
    findConsistent'' (filter ((/=) (dcName dc) . dcName) dcs) pc
findConsistent'' dcs ((ConsCond dc _ True):pc) =
    findConsistent'' (filter ((==) (dcName dc) . dcName) dcs) pc
findConsistent'' dcs ((ConsCond  dc _ False):pc) =
    findConsistent'' (filter ((/=) (dcName dc) . dcName) dcs) pc
findConsistent'' dcs [] = Just dcs
findConsistent'' _ _ = Nothing


-- Various helper functions

isExtCond :: PathCond -> Bool
isExtCond (ExtCond _ _) = True
isExtCond _ = False

pcVarType :: [PathCond] -> Maybe Name
pcVarType (AltCond _ (Var (Id _ (TyConApp n _))) _:pc) = pcVarType' n pc
pcVarType (ConsCond _ (Var (Id _ (TyConApp n _))) _:pc) = pcVarType' n pc
pcVarType _ = Nothing

pcVarType' :: Name -> [PathCond] -> Maybe Name
pcVarType' n (AltCond _ (Var (Id _ (TyConApp n' _))) _:pc) =
    if n == n' then pcVarType' n pc else Nothing
pcVarType' n (ConsCond _ (Var (Id _ (TyConApp n' _))) _:pc) =
    if n == n' then pcVarType' n pc else Nothing
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
replaceReturnType (TyForAll _ t) r = replaceReturnType t r
replaceReturnType (TyFun t1 t2@(TyFun _ _)) r = TyFun t1 $ replaceReturnType t2 r
replaceReturnType (TyFun t _) r = TyFun t r
replaceReturnType _ r = r