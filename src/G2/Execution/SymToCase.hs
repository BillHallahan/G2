module G2.Execution.SymToCase (createCaseExpr, createCaseExprInsertless) where

import G2.Execution.DataConPCMap
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L

-- | Creates and applies new symbolic variables for arguments of Data Constructor
concretizeSym :: TyVarEnv -> [(Id, Type)] -> Maybe Coercion -> Id -> KnownValues -> TypeEnv
              -> ([(Name, Expr)], [Id], NameGen) -> DataCon -> (([(Name, Expr)], [Id], NameGen), ([PathCond], Expr))
concretizeSym tv bi maybeC binder kv tenv (concs, syms, ng) dc@(DataCon _ ts _ _)
    | Just dcpcs <- HM.lookup (dcName dc) (dcpcMap tv kv tenv)
    , _:ty_args <- unTyApp $ typeOf tv binder
    , Just dcpc <- L.lookup ty_args dcpcs =
        let (pcs, ng'', _, dcpc_concs, dcpc_syms) = applyDCPC ng' new_params (Var binder) dcpc
        in ((concs ++ dcpc_concs, syms ++ new_params ++ dcpc_syms, ng''), (pcs, dc''))

    | otherwise = ((concs, syms ++ new_params, ng'), ([], dc''))
    where
        ts' = foldr (\(i, t) e -> retype i t e) (anonArgumentTypes ts) bi
        (new_params, ng') = freshIds ts' ng
        dc' = mkApp $ Data dc : map (Type . snd) bi ++ map Var new_params
        dc'' = case maybeC of
            (Just (t1 :~ t2)) -> Cast dc' (t2 :~ t1)
            Nothing -> dc'

createCaseExpr' :: KnownValues -> Id -> Type -> [([PathCond], Expr)] -> (Expr, [PathCond])
createCaseExpr' _ _ _ [(pc, e)] = (e, pc)
createCaseExpr' kv new_id t es@(_:_) =
    let
        -- We assume that PathCond restricting new_id's range is added elsewhere
        alts = zipWith (\num (_, e) ->
                            Alt (LitAlt (LitInt num)) e) [0..] es
        pcs = concat $ zipWith (\num (pc, _) -> map (addImp num) pc) [0..] es
    in (Case (Var new_id) new_id t alts, pcs)
    where
        addImp num (ExtCond e b) =
            ExtCond (mkApp
                        [ mkImpliesPrim kv
                        , mkApp [mkEqPrimInt kv, Var new_id, Lit $ LitInt num]
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
    let (new_id, mexpr, pcs, ng', concs, syms) = createCaseExprInsertless tv bi maybeC binder ti kv tenv ng dcs
        eenv' = E.insertExprs concs $ L.foldl' (flip E.insertSymbolic) eenv syms
    in (new_id, mexpr, pcs, eenv', ng')

-- Make a case expression, returning lists of what to insert instead of inserting
createCaseExprInsertless :: TyVarEnv 
                         -> [(Id, Type)]
                         -> Maybe Coercion
                         -> Id
                         -> Type -- ^ Return type of case expression
                         -> KnownValues
                         -> TypeEnv
                         -> NameGen
                         -> [DataCon]
                         -> (Id, Expr, [PathCond], NameGen, [(Name, Expr)], [Id])
createCaseExprInsertless tv bi maybeC binder ti kv tenv ng dcs =
    let
        (new_id, ng') = freshId TyLitInt ng
        ((concs, syms, ng''), dcs') = L.mapAccumL (concretizeSym tv bi maybeC binder kv tenv) ([], [], ng') dcs

        -- Create a case expression to choose on of viable DCs
        (mexpr', assume_pc) = createCaseExpr' kv new_id ti dcs'
        -- add PC restricting range of values for newSymId
        newSymConstraint = restrictSymVal tv kv 0 (toInteger $ length dcs' - 1) new_id
    in
    (new_id, mexpr', newSymConstraint:assume_pc, ng'', concs, new_id:syms)

-- | Return PathCond restricting value of `new_id` to [lower, upper]
restrictSymVal :: TyVarEnv -> KnownValues -> Integer -> Integer -> Id -> PathCond
restrictSymVal tv kv lower upper new_id
    | lower /= upper =
        ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var new_id) lower) (mkLeIntExpr kv (Var new_id) upper)) True
    | otherwise = ExtCond (mkEqExpr tv kv (Var new_id) (Lit $ LitInt lower)) True
