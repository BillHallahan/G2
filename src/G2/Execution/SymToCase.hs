module G2.Execution.SymToCase (createCaseExpr) where

import G2.Execution.DataConPCMap
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L

-- | Creates and applies new symbolic variables for arguments of Data Constructor
concretizeSym :: TyVarEnv -> [(Id, Type)] -> Maybe Coercion -> Id -> KnownValues -> TypeEnv
              -> (ExprEnv, NameGen) -> DataCon -> ((ExprEnv, NameGen), ([PathCond], Expr))
concretizeSym tv bi maybeC binder kv tenv (eenv, ng) dc@(DataCon _ ts _ _)
    | Just dcpcs <- HM.lookup (dcName dc) (dcpcMap tv kv tenv)
    , _:ty_args <- unTyApp $ typeOf tv binder
    , Just dcpc <- L.lookup ty_args dcpcs =
        let 
            (eenv'', pcs, ng'', _) = applyDCPC ng' eenv' newParams (Var binder) dcpc
        in
        ((eenv'', ng''), (pcs, dc''))

    | otherwise = ((eenv', ng'), ([], dc''))
    where
        ts' = foldr (\(i, t) e -> retype i t e) (anonArgumentTypes ts) bi
        (newParams, ng') = freshIds ts' ng
        dc' = mkApp $ Data dc : map (Type . snd) bi ++ map Var newParams
        dc'' = case maybeC of
            (Just (t1 :~ t2)) -> Cast dc' (t2 :~ t1)
            Nothing -> dc'
        eenv' = foldr E.insertSymbolic eenv newParams

createCaseExpr' :: KnownValues -> Id -> Type -> [([PathCond], Expr)] -> (Expr, [PathCond])
createCaseExpr' _ _ _ [(pc, e)] = (e, pc)
createCaseExpr' kv newId t es@(_:_) =
    let
        -- We assume that PathCond restricting newId's range is added elsewhere
        alts = zipWith (\num (_, e) ->
                            Alt (LitAlt (LitInt num)) e) [0..] es
        pcs = concat $ zipWith (\num (pc, _) -> map (addImp num) pc) [0..] es
    in (Case (Var newId) newId t alts, pcs)
    where
        addImp num (ExtCond e b) =
            ExtCond (mkApp
                        [ mkImpliesPrim kv
                        , mkApp [mkEqPrimInt kv, Var newId, Lit $ LitInt num]
                        , e]) b
        addImp _ _ = error "addImp: Unsupported path constraints"
createCaseExpr' kv _ _ [] = (Prim Undefined TyBottom, [ExtCond (mkFalse kv) True])

createCaseExpr :: TyVarEnv 
               -> [(Id, Type)]
               -> Maybe Coercion
               -> Id
               -> Type -- ^ Return type of case expression
               -> KnownValues
               -> TypeEnv
               -> ExprEnv
               -> NameGen
               -> [DataCon]
               -> (Id, Expr, [PathCond], ExprEnv, NameGen)
createCaseExpr tv bi maybeC binder ti kv tenv eenv ng dcs =
    let
        (newId, ng') = freshId TyLitInt ng
        eenv' = E.insertSymbolic newId eenv

        ((eenv'', ng''), dcs') = L.mapAccumL (concretizeSym tv bi maybeC binder kv tenv) (eenv', ng') dcs

        -- Create a case expression to choose on of viable DCs
        (mexpr', assume_pc) = createCaseExpr' kv newId ti dcs'
        -- add PC restricting range of values for newSymId
        newSymConstraint = restrictSymVal tv kv 0 (toInteger $ length dcs' - 1) newId

    in
    (newId, mexpr', newSymConstraint:assume_pc, eenv'', ng'')

-- | Return PathCond restricting value of `newId` to [lower, upper]
restrictSymVal :: TyVarEnv -> KnownValues -> Integer -> Integer -> Id -> PathCond
restrictSymVal tv kv lower upper newId
    | lower /= upper =
        ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var newId) lower) (mkLeIntExpr kv (Var newId) upper)) True
    | otherwise = ExtCond (mkEqExpr tv kv (Var newId) (Lit $ LitInt lower)) True
