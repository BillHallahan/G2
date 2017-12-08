module G2.Internals.Solver.ADTSolver ( checkConsistency
									 , findConsistent) where

import G2.Internals.Language.Casts
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.PathConds
import G2.Internals.Language.TypeEnv
import G2.Internals.Language.Typing

import Prelude hiding (null)
import qualified Prelude as Pre

-- | checkConsistency
-- Attempts to detemine if the given PathConds are consistent.
-- Returns Just True if they are, Just False if they are not,
-- and Nothing if it can't decide.
checkConsistency :: TypeEnv -> PathConds -> Maybe Bool
checkConsistency tenv pc = maybe Nothing (Just . not . Pre.null) $ findConsistent tenv pc

-- | findConsistent
-- Attempts to find expressions (Data d) or (Coercion (Data d), (t1 :~ t2)) consistent with the given path
-- constraints.  Returns Just [...] if it can determine [...] are consistent.
-- Just [] means there are no consistent Expr.  Nothing nmeans it could not be
-- determined if there were any consistent data constructors.
-- In practice, the result should always be Just [...] if all the path conds
-- are about ADTs.
findConsistent :: TypeEnv -> PathConds -> Maybe [Expr]
findConsistent tenv pc =
    let
        pc' = unsafeElimCast $ toList pc

        -- Adding Coercions
        pcNT = pcInCastType . head $ toList pc
        cons = findConsistent' tenv pc'

        cons' = fmap (simplifyCasts . map (castReturnType pcNT)) cons 
    in
    if any isExtCond pc' then Nothing else cons'

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
replaceReturnType (TyFun t1 t2@(TyFun _ _)) r = TyFun t1 $ replaceReturnType t2 r
replaceReturnType (TyFun t _) r = TyFun r t
replaceReturnType _ r = r

dcName :: DataCon -> Name
dcName (DataCon n _ _) = n
dcName _ = error "Invalid DataCon in dcName"