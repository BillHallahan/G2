module G2.Execution.StateMerging
  ( mergeState
  , mergeCurrExpr
  , mergeExpr
  , mergeExprEnv
  , mergeEnvObj
  , mergePathConds
  , mergePathCondsSimple
  , emptyContext
  , Context
  , createCaseExpr
  , bindExprToNum
  , implies
  ) where

import G2.Language
import G2.Execution.NormalForms
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.PathConds as PC

import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.HashSet as HS
import qualified Data.HashMap.Strict as HM

isMergeable :: Eq t => State t -> State t -> Bool
isMergeable s1 s2 = 
    (exec_stack s1 == exec_stack s2)
    && (isMergeableCurrExpr (expr_env s1) (expr_env s2) (curr_expr s1) (curr_expr s2))
    && (type_env s1 == type_env s2)
    && (known_values s1 == known_values s2)
    && (non_red_path_conds s1 == non_red_path_conds s2)
    && (true_assert s1 == true_assert s2)
    && (assert_ids s1 == assert_ids s2)
    && (tags s1 == tags s2)
    && (track s1 == track s2)
    && (type_classes s1 == type_classes s2)
    && (isEmpty $ model s1)
    && (isEmpty $ model s2)

isMergeableCurrExpr :: E.ExprEnv -> E.ExprEnv -> CurrExpr -> CurrExpr -> Bool
isMergeableCurrExpr eenv1 eenv2 (CurrExpr Evaluate ce1) (CurrExpr Evaluate ce2) = isMergeableExpr eenv1 eenv2 ce1 ce2
isMergeableCurrExpr eenv1 eenv2 (CurrExpr Return ce1) (CurrExpr Return ce2) = isMergeableExpr eenv1 eenv2 ce1 ce2
isMergeableCurrExpr _ _ _ _ = False

-- | Returns True if both Exprs are of the form (App ... (App (Data DataCon)) ....) or (App ... (App (Var x)) ...), where (Var x) is a Symbolic variable
isMergeableExpr :: E.ExprEnv -> E.ExprEnv -> Expr -> Expr -> Bool
isMergeableExpr eenv1 eenv2 (App e1 _) (App e1' _) = isMergeableExpr eenv1 eenv2 e1 e1'
isMergeableExpr _ _ (Data dc1) (Data dc2) = dc1 == dc2
isMergeableExpr eenv1 eenv2 (Var i1) (Var i2)
    | (Just (E.Sym _)) <- E.lookupConcOrSym (idName i1) eenv1
    , (Just (E.Sym _)) <- E.lookupConcOrSym (idName i2) eenv2 = True
isMergeableExpr _ _ _ _ = False

-- | Values that are passed around and updated while merging individual fields in 2 States
data Context t = Context { renamed1_ :: HM.HashMap Name Name -- Map from old Names in State `s1_` to new Names
                         , renamed2_ :: HM.HashMap Name Name
                         , new_names1_ :: HM.HashMap Name Name -- Optimization: Newly renamed Names in State `s1_`, not yet added to `renamed1_`
                         , new_names2_ :: HM.HashMap Name Name -- so that we can call renames with only new_names*_, not all renamed*_ names
                         , s1_ :: State t
                         , s2_ :: State t
                         , ng_ :: NameGen
                         , newId_ :: Id -- `newId` is set to 1 or 2 in an AssumePC/ Case Expr when merging values from `s1_` or `s2_` respectively
                         , newPCs_ :: [PathCond]
                         , newSyms_ :: SymbolicIds -- Newly added symbolic variables when merging Exprs
                         }

-- | Copies values from `new_names*__` to the respective `renamed*_` fields and clears `new_names*_`
moveNewNames :: Context t -> Context t
moveNewNames ctxt@(Context { renamed1_ = renamed1
                            , renamed2_ = renamed2
                            , new_names1_ = newNames1
                            , new_names2_ = newNames2 }) =
    let renamed1' = HM.union renamed1 newNames1
        renamed2' = HM.union renamed2 newNames2
        newNames1' = HM.empty
        newNames2' = HM.empty
    in ctxt { renamed1_ = renamed1', renamed2_ = renamed2', new_names1_ = newNames1', new_names2_ = newNames2' }

emptyContext :: State t -> State t -> NameGen -> Id -> Context t
emptyContext s1 s2 ng newId = Context { renamed1_ = HM.empty
                                      , renamed2_ = HM.empty
                                      , new_names1_ = HM.empty
                                      , new_names2_ = HM.empty
                                      , s1_ = s1
                                      , s2_ = s2
                                      , ng_ = ng
                                      , newId_ = newId
                                      , newPCs_ = []
                                      , newSyms_ = HS.empty}

mergeState :: (Eq t, Named t) => NameGen -> State t -> State t -> (NameGen, Maybe (State t))
mergeState ngen s1 s2 = 
    if isMergeable s1 s2
        then 
            let (newId, ngen') = freshId TyLitInt ngen
                ctxt = emptyContext s1 s2 ngen' newId
                (ctxt', curr_expr') = mergeCurrExpr ctxt
                (ctxt'', eenv') = mergeExprEnv ctxt'
                path_conds' = mergePathCondsSimple ctxt''
                syms' = mergeSymbolicIds ctxt''
                s1' = s1_ ctxt''
                ngen'' = ng_ ctxt''
            in (ngen''
               , (Just State { expr_env = eenv'
                             , type_env = type_env s1'
                             , curr_expr = curr_expr'
                             , path_conds = path_conds'
                             , non_red_path_conds = non_red_path_conds s1'
                             , true_assert = true_assert s1'
                             , assert_ids = assert_ids s1'
                             , type_classes = type_classes s1'
                             , symbolic_ids = syms'
                             , exec_stack = exec_stack s1'
                             , model = model s1'
                             , known_values = known_values s1'
                             , rules = rules s1'
                             , num_steps = num_steps s1'
                             , track = track s1'
                             , tags = tags s1' }))
        else (ngen, Nothing)

mergeCurrExpr :: Named t => Context t -> (Context t, CurrExpr)
mergeCurrExpr ctxt@(Context { s1_ = (State {curr_expr = ce1}), s2_ = (State {curr_expr = ce2}) })
    | (CurrExpr evalOrRet1 e1) <- ce1
    , (CurrExpr evalOrRet2 e2) <- ce2
    , evalOrRet1 == evalOrRet2 =
        let (ctxt', ce') = mergeExprInline ctxt e1 e2
        in (ctxt', CurrExpr evalOrRet1 ce')
    | otherwise = error "The curr_expr(s) have an invalid form and cannot be merged."

-- | Merges 2 Exprs, combining 2 corresponding symbolic Vars into 1 if possible, and substituting the full Expr of any concrete Vars
-- Also returns any newly added Symbolic Variables and Names of renamed Variables
mergeExprInline :: Named t
                => Context t -> Expr -> Expr
                -> (Context t, Expr)
mergeExprInline ctxt (App e1 e2) (App e3 e4) =
    let (ctxt', e1') = mergeExprInline ctxt e1 e3
        -- For any symbolic variable pairs merged into new variables when merging `e1` and `e3`, rename all occurrences of
        -- the old symbolic vars in `e2` and `e4`
        e2' = renames (new_names1_ ctxt') e2
        e4' = renames (new_names2_ ctxt') e4
        -- move names from newNames to renamed
        ctxt'' = moveNewNames ctxt'
        (ctxt''', e2'') = mergeExprInline ctxt'' e2' e4'
        ctxt'''' = ctxt''' { new_names1_ = HM.union (new_names1_ ctxt') (new_names1_ ctxt''')
                           , new_names2_ = HM.union (new_names2_ ctxt') (new_names2_ ctxt''') }
    in (ctxt'''', App e1' e2'')
mergeExprInline ctxt e1@(App _ _) (Var i) = mergeVarInline ctxt i e1 False
mergeExprInline ctxt (Var i) e2@(App _ _) = mergeVarInline ctxt i e2 True
mergeExprInline ctxt@(Context { s1_ = s1, s2_ = s2 }) e1@(Var i1) e2@(Var i2)
    | e1 == e2 = (ctxt, e1)
    | otherwise =
        let maybeE1' = E.lookupConcOrSym (idName i1) (expr_env s1)
            maybeE2' = E.lookupConcOrSym (idName i2) (expr_env s2)
        in mergeVarsInline ctxt maybeE1' maybeE2'
mergeExprInline ctxt@(Context { s1_ = s1, s2_ = s2 }) e1@(Case _ _ _) e2
    | isSMNF (expr_env s1) e1
    , isSMNF (expr_env s2) e2 = mergeCase ctxt e1 e2
mergeExprInline ctxt@(Context { s1_ = s1, s2_ = s2 }) e1 e2@(Case _ _ _)
    | isSMNF (expr_env s1) e1
    , isSMNF (expr_env s2) e2 = mergeCase ctxt e1 e2
mergeExprInline ctxt@(Context { newId_ = newId }) e1 e2
    | e1 == e2 = (ctxt, e1)
    | otherwise =
        let mergedExpr = createCaseExpr newId [e1, e2]
        in (ctxt, mergedExpr)

mergeVarInline :: (Named t)
               => Context t -> Id -> Expr -> Bool
               -> (Context t, Expr)
mergeVarInline ctxt@(Context { s1_ = s1, s2_ = s2, newId_ = newId }) i e@(App _ _) first =
    let eenv = if first
            then expr_env s1
            else expr_env s2
        maybeE = E.lookupConcOrSym (idName i) eenv
    in case maybeE of
        (Just (E.Conc e')) -> if first
            then mergeExprInline ctxt e' e
            else mergeExprInline ctxt e e'
        (Just (E.Sym iSym)) ->
            let mergedExpr = if first
                then createCaseExpr newId [(Var iSym), e]
                else createCaseExpr newId [e, (Var iSym)]
            in (ctxt, mergedExpr)
        Nothing -> error $ "Unable to find Var in expr_env: " ++ show i
mergeVarInline _ _ _ _ = error "mergeVarInline can only merge an Id with Expr of the form 'App _ _'"

mergeVarsInline :: Named t
                => Context t -> Maybe E.ConcOrSym -> Maybe E.ConcOrSym
                -> (Context t, Expr)
mergeVarsInline ctxt@(Context {s1_ = s1, s2_ = s2, renamed1_ = renamed1, renamed2_ = renamed2, ng_ = ng, newId_ = newId}) maybeE1 maybeE2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 = mergeExprInline ctxt e1 e2
    | (Just (E.Conc e1)) <- maybeE1
    , (Just (E.Sym i)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId [e1, (Var i)]
        in (ctxt, mergedExpr)
    | (Just (E.Sym i)) <- maybeE1
    , (Just (E.Conc e2)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId [(Var i), e2]
        in (ctxt, mergedExpr)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , i1 == i2 = (ctxt, Var i1)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , (idType i1 == idType i2)
    , not $ HS.member i1 (symbolic_ids s2)
    , not $ HS.member i2 (symbolic_ids s1) = -- if both are symbolic variables unique to their states, replace one of them with the other
        let s2' = rename (idName i2) (idName i1) s2
            syms' = HS.insert i1 (HS.delete i2 (symbolic_ids s2))
            s2'' = s2' {symbolic_ids = syms'}
            ctxt' = ctxt { s2_ = s2'', new_names2_ = HM.singleton (idName i2) (idName i1) }
        in (ctxt', Var i1)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2
    , idType i1 == idType i2
    , not $ elem (idName i1) (HM.elems renamed1) -- check if symbolic var is a var that is a result of some previous renaming when merging the Expr
    , not $ elem (idName i2) (HM.elems renamed2) =
        let (newSymId, ng') = freshId (idType i1) ng
            s1' = rename (idName i1) (idName newSymId) s1
            s2' = rename (idName i2) (idName newSymId) s2
            syms1' = HS.insert newSymId (HS.delete i1 (symbolic_ids s1))
            syms2' = HS.insert newSymId (HS.delete i2 (symbolic_ids s2))
            s1'' = s1' {symbolic_ids = syms1'}
            s2'' = s2' {symbolic_ids = syms2'}
            ctxt' = ctxt {ng_ = ng', s1_ = s1'', s2_ = s2'', new_names1_ = HM.singleton (idName i1) (idName newSymId)
                         , new_names2_ = HM.singleton (idName i2) (idName newSymId) }
        in (ctxt', Var newSymId)
    | (Just (E.Sym i1)) <- maybeE1
    , (Just (E.Sym i2)) <- maybeE2 =
        let mergedExpr = createCaseExpr newId [(Var i1), (Var i2)]
        in (ctxt, mergedExpr)
    | otherwise = error "Unable to find Var(s) in expr_env"

type Conds = [(Id, Integer)]

-- | Given 2 Exprs such as:
-- Case n of (1 -> A e f, 2 -> B g h), and
-- Case m of (1 -> B g f, 2 -> A f h), merges them to form:
-- Case new of
--      1 -> A (Case new' of 1 -> e, 2 -> f) (Case new'' of 1 -> f, 2 -> h)
--      2 -> B g (Case new''' of 1 -> h, 2 -> f)
-- With new PathConds:
-- NOT (new = 1) OR ((NOT (new' = 1) OR (n = 1)) AND (NOT (new' = 1) OR (m = 2)) AND (NOT (new'' = 1) OR (n = 1)) AND (NOT (new'' = 2) OR (m = 2)))
-- NOT (new = 2) OR ((NOT (new''' = 1) OR (n = 2)) AND (NOT (new''' = 2) OR (m = 1)))
mergeCase :: Named t
          => Context t -> Expr -> Expr
          -> (Context t, Expr)
mergeCase ctxt@(Context { newId_ = newId}) e1 e2 =
    let choices = (getChoices e1 newId 1) ++ (getChoices e2 newId 2)
    in mergeCase' ctxt choices

mergeCase' :: Named t
          => Context t -> [(Conds, Expr)]
          -> (Context t, Expr)
mergeCase' ctxt@(Context { s1_ = s1@(State {known_values = kv}), s2_ = s2, ng_ = ng, newId_ = newId, newPCs_ = newPCs, newSyms_ = syms }) choices =
    let groupedChoices = groupChoices choices
        (ctxt', merged) = L.mapAccumR mergeChoices (emptyContext s1 s2 ng newId) groupedChoices

        newSyms = newSyms_ ctxt'
        ng' = ng_ ctxt'
        (newSymId, ng'') = freshId TyLitInt ng'
        newSyms' = HS.insert newSymId newSyms

        mergedExprs = map fst merged
        mergedExpr = createCaseExpr newSymId mergedExprs
        newPCs' = map snd merged
        (upper, newPCs'') = bindExprToNum (\num pc -> impliesPC kv newSymId num pc) newPCs' -- note: binding here is same as in createCaseExpr

        -- add PC restricting range of values for newSymId
        lower = 1
        newSymConstraint = ExtCond (mkAndExpr kv (mkGeIntExpr kv (Var newSymId) lower) (mkLeIntExpr kv (Var newSymId) (upper - 1))) True
        newPCs''' = newSymConstraint:newPCs''
        ctxt'' = ctxt {newPCs_ = newPCs''' ++ newPCs, newSyms_ = HS.union newSyms' syms, ng_ = ng''}
    in (ctxt'', mergedExpr)

-- | Given a list of (Conds, Expr) with the same inner DataCon, merges the Exprs recursively into 1 Expr, along with an associated PathCond
-- formed from the given Conds
mergeChoices :: Named t => Context t -> [(Conds, Expr)] -> (Context t, (Expr, PathCond))
mergeChoices ctxt@(Context {s1_ = (State { known_values = kv }) }) [choice] =
    let pc = ExtCond (condsToExpr kv (fst choice)) True
    in (ctxt , (snd choice, pc))
mergeChoices ctxt@(Context { s1_ = (State { known_values = kv}) }) choices@(_:_) =
        -- apps :: [(Conds, [Expr])], split up each choice into a sequence of sub-Exprs
    let apps = map (\(cs, e) -> (cs, unApp e)) choices
        -- appsWConds :: [[(Conds, Expr)]], for each `[Expr]` in apps, pair the common `Conds` with each `Expr` in the list
        appsWConds = map (\(cs, e) -> map (\x -> (cs, x)) e) apps
        -- appsWCondsT :: [[(Conds, Expr)]], where each `[(Conds, Expr)]` is a list of choices for that sub-Expr in the merged Expr
        appsWCondsT = L.transpose appsWConds
        -- split the appsWCondsT into 2 lists, where first list contains sub-Exprs that are equal among all the choices
        (common, rest) = L.span (\ls -> (length . L.nub $ (map snd ls)) == 1) appsWCondsT
        (ctxt', restMerged) = L.mapAccumR mergeCase' ctxt rest
        -- get just the Exprs (add PathConds later)
        common' = map (snd . head) common
        apps' = common' ++ restMerged
        mergedExpr = mkApp apps'

        newPCs = case restMerged of
            -- 'AND' all `Conds` for each Expr and `OR` these combined Conds together
            [] -> (\e -> [ExtCond e True]) . dnf kv $ map (condsToExpr kv . fst) choices
            _ -> newPCs_ ctxt' -- PCs would have been added when merging tailApps
        newPCExprs = map (\(ExtCond e _) -> e) newPCs
        newPC = ExtCond (cnf kv newPCExprs) True
        ctxt'' = ctxt' {newPCs_ = []}
    in (ctxt'', (mergedExpr, newPC))
mergeChoices _ [] = error $ "Choices must be non empty"

-- | If `e` is a Case Expr, recursively gets list of nested Alt Exprs, along with (Id, Integer) pairs indicating the accumulated constraints
-- along the way. (Assumed that `e` is in SMNF)
-- e.g. getChoices Case x of (1 -> Case y of (1 -> A, 2 -> B), 2 -> Case z of (1 -> C, 2 -> D (Case w of 1 -> E, 2 -> F))) =
-- [([(x,1), (y,1)], A), ([(x,1), (y,2)], B), ([(x,2),(z,1)], C), ([(x,2),(z,2)], D (Case w of 1 -> E, 2 -> F))]
getChoices :: Expr -> Id -> Integer -> [(Conds, Expr)]
getChoices e newId num
    | (Case (Var i) _ a) <- e =
        let choices = concatMap (getChoices' i) a
            choices' = map (\(c, ex) -> (cond:c, ex)) choices
        in choices'
    | otherwise = [([cond], e)]
    where
        cond = (newId, num)

getChoices' :: Id -> Alt -> [(Conds, Expr)]
getChoices' i (Alt (LitAlt (LitInt l)) e) =
    let cond = (i, l)
        choices = getChoices'' e
        choices' = map (\(c, ex) -> (cond:c, ex)) choices
    in choices'
getChoices' alt _ = error $ "Unhandled Alt: " ++ (show alt)

getChoices'' :: Expr -> [(Conds, Expr)]
getChoices'' (Case (Var i) _ a) = concatMap (getChoices' i) a
getChoices'' e = [([], e)]

groupChoices :: [(Conds, Expr)] -> [[(Conds, Expr)]]
groupChoices xs = L.groupBy (\(_, e1) (_, e2) -> sameDataCon e1 e2) xs

sameDataCon :: Expr -> Expr -> Bool
sameDataCon (App e1 _) (App e1' _) = sameDataCon e1 e1'
sameDataCon (Data dc1) (Data dc2) = dc1 == dc2
sameDataCon e1 e2 = e1 == e2

-- Given list of (Id, Int) pairs, creates Expr equivalent to Conjunctive Normal Form of (Id == Int) values
condsToExpr :: KnownValues -> Conds -> Expr
condsToExpr kv c =
    let es = map (\(i, num) -> mkEqIntExpr kv (Var i) num) c
    in cnf kv es

-- Given an `ExtCond e b`, and an `Id`, `Int` pair, modifies `e` to (NOT (Id == Int)) OR e
impliesPC :: KnownValues -> Id -> Integer -> PathCond -> PathCond
impliesPC kv newId num (ExtCond e b) = implies kv newId num e b
impliesPC _ _ _ pc = error $ "Can only add clause to ExtCond. Got: " ++ (show pc)

-- Given an Expr `e`, and an `Id`, `Int` pair, returns `ExtCond ((NOT (Id == Int)) OR e) True`
implies :: KnownValues -> Id -> Integer -> Expr -> Bool -> PathCond
implies kv newId num e b = implies' kv (mkEqIntExpr kv (Var newId) num) e b

implies' :: KnownValues -> Expr -> Expr -> Bool -> PathCond
implies' kv clause e b =
    let e' = mkOrExpr kv (mkNotExpr kv clause) e
    in ExtCond e' b

-- | Merges 2 Exprs without inlining Vars from the expr_env or combining symbolic variables
-- Given 2 Exprs equivalent to "D e_1, e_2, ..., e_n" and "D e_1', e_2',..., e_n' ", returns a merged Expr equivalent to
-- "D NonDet[(Assume (x == 1) in e_1), (Assume (x == 2) in e_1')],..., NonDet[(Assume (x == 1) in e_n), (Assume (x == 2) in e_n')]" 
mergeExpr :: Id -> Expr -> Expr -> Expr
mergeExpr newId (App e1 e2) (App e1' e2') = App (mergeExpr newId e1 e1') (mergeExpr newId e2 e2')
mergeExpr newId e1 e1' = if (e1 == e1')
    then e1
    else createCaseExpr newId [e1, e1']

createCaseExpr :: Id -> [Expr] -> Expr
createCaseExpr _ [e] = e
createCaseExpr newId es@(_:_) =
    let
        -- We assume that PathCond restricting newId's range is added elsewhere
        (_, alts) = bindExprToNum (\num e -> Alt (LitAlt (LitInt num)) e) es
    in Case (Var newId) newId alts
createCaseExpr _ [] = error "No exprs"

bindExprToNum :: (Integer -> a -> b) -> [a] -> (Integer, [b])
bindExprToNum f es = L.mapAccumL (\num e -> (num + 1, f num e)) 1 es

mergeSymbolicIds :: Context t -> SymbolicIds
mergeSymbolicIds (Context { s1_ = (State {symbolic_ids = syms1}), s2_ = (State {symbolic_ids = syms2})
                          , newSyms_ = syms3, newId_ = newId}) =
    let
        syms' = HS.unions [syms1, syms2, syms3]
        syms'' = HS.insert newId syms'
    in syms''


-- | Keeps all EnvObjs found in only one ExprEnv, and combines the common (key, value) pairs using the mergeEnvObj function
mergeExprEnv :: Context t -> (Context t, E.ExprEnv)
mergeExprEnv ctxt@(Context {s1_ = (State {expr_env = eenv1}), s2_ = (State {expr_env = eenv2}), newId_ = newId, ng_ = ngen}) =
    let
        eenv1_map = E.unwrapExprEnv eenv1
        eenv2_map = E.unwrapExprEnv eenv2
        zipped_maps = (M.intersectionWith (\a b -> (a,b)) eenv1_map eenv2_map)
        ((changedSyms1, changedSyms2, ngen'), merged_map) = M.mapAccum (mergeEnvObj newId eenv1 eenv2) (HM.empty, HM.empty, ngen) zipped_maps
        newSyms = (HM.elems changedSyms1) ++ (HM.elems changedSyms2)
        merged_map' = foldr (\i@(Id n _) m -> M.insert n (E.SymbObj i) m) merged_map newSyms
        eenv1_rem = (M.difference eenv1_map eenv2_map)
        eenv2_rem = (M.difference eenv2_map eenv1_map)
        eenv' = E.wrapExprEnv $ M.unions [merged_map', eenv1_rem, eenv2_rem]

        ctxt' = ctxt {ng_ = ngen'}
        -- rename any old Syms in PathConds in each state to their new Names, based on list of pairs in changedSyms1_ and changedSyms2_
        ctxt'' = updatePCs ctxt' changedSyms1 changedSyms2
        ctxt''' = updateSymbolicIds ctxt'' changedSyms1 changedSyms2
    in (ctxt''', eenv')

mergeEnvObj :: Id -> E.ExprEnv -> E.ExprEnv -> (HM.HashMap Id Id, HM.HashMap Id Id, NameGen) -> (E.EnvObj, E.EnvObj)
            -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeEnvObj newId eenv1 eenv2 (changedSyms1, changedSyms2, ngen) (eObj1, eObj2)
    | eObj1 == eObj2 = ((changedSyms1, changedSyms2, ngen), eObj1)
    -- Following cases deal with unequal EnvObjs
    | (E.ExprObj e1) <- eObj1
    , (E.ExprObj e2) <- eObj2 = ((changedSyms1, changedSyms2, ngen), E.ExprObj (mergeExpr newId e1 e2))
    -- Replace the Id in the SymbObj with a new Symbolic Id and merge with the expr from the ExprObj in a NonDet expr
    | (E.SymbObj i) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.SymbObj i) <- eObj2 = mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i e1 False
    -- Lookup RedirObj and create a NonDet Expr combining the lookup result with the expr from the ExprObj
    | (E.RedirObj n) <- eObj1
    , (E.ExprObj e2) <- eObj2 = mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv1 n e2 True
    | (E.ExprObj e1) <- eObj1
    , (E.RedirObj n) <- eObj2 = mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv2 n e1 False
    | (E.RedirObj n1) <- eObj1
    , (E.RedirObj n2) <- eObj2 = mergeTwoRedirObjs ngen changedSyms1 changedSyms2 newId eenv1 eenv2 n1 n2
    -- case of same name pointing to unequal SymbObjs shouldn't occur
    | (E.SymbObj i1) <- eObj1
    , (E.SymbObj i2) <- eObj2 = mergeTwoSymbObjs ngen changedSyms1 changedSyms2 newId i1 i2
    | otherwise = error $ "Unequal SymbObjs or RedirObjs present in the expr_envs of both states." ++ (show eObj1) ++ " " ++ (show eObj2)

-- | If same name `n` points to a symbolic x@(Var (Id n _)) and Expr `e` in the 2 states, replace `x` with new symbolic variable `x'` and merge
-- both `e` and `x'`
mergeSymbExprObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> Id -> Expr -> Bool
                  -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeSymbExprObjs ngen changedSyms1 changedSyms2 newId i@(Id _ t) e first =
        let (newSymId, ngen') = freshId t ngen
        -- Bool @`first` signifies which state the Id/Expr belongs to. Needed to ensure they are enclosed under the right `Assume` in the NonDet Exprs
        in case first of
            True ->
                let changedSyms1' = HM.insert i newSymId changedSyms1
                    mergedExprObj = E.ExprObj (mergeExpr newId (Var newSymId) e)
                in ((changedSyms1', changedSyms2, ngen'), mergedExprObj)
            False ->
                let changedSyms2' = HM.insert i newSymId changedSyms2
                    mergedExprObj = E.ExprObj (mergeExpr newId e (Var newSymId))
                in ((changedSyms1, changedSyms2', ngen'), mergedExprObj)

mergeRedirExprObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> E.ExprEnv -> Name -> Expr -> Bool
                   -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeRedirExprObjs ngen changedSyms1 changedSyms2 newId eenv n e first =
        let e2 = case (E.lookup n eenv) of
                Just x -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n)
            mergedEObj = case first of
                True -> E.ExprObj (mergeExpr newId e2 e)
                False -> E.ExprObj (mergeExpr newId e e2)
        in ((changedSyms1, changedSyms2, ngen), mergedEObj)

mergeTwoRedirObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> E.ExprEnv -> E.ExprEnv -> Name -> Name
                  -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoRedirObjs ngen changedSyms1 changedSyms2 newId eenv1 eenv2 n1 n2 =
        let e1 = case (E.lookup n1 eenv1) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n1)
            e2 = case (E.lookup n2 eenv2) of
                (Just x) -> x
                Nothing -> error $ "Could not find EnvObj with name: " ++ (show n2)
            mergedExprObj = E.ExprObj (mergeExpr newId e1 e2)
        in ((changedSyms1, changedSyms2, ngen), mergedExprObj)

mergeTwoSymbObjs :: NameGen -> HM.HashMap Id Id -> HM.HashMap Id Id -> Id -> Id -> Id
                 -> ((HM.HashMap Id Id, HM.HashMap Id Id, NameGen), E.EnvObj)
mergeTwoSymbObjs ngen changedSyms1 changedSyms2 newId i1@(Id _ t1) i2@(Id _ t2) =
        let (newSymId1, ngen') = freshId t1 ngen
            (newSymId2, ngen'') = freshId t2 ngen'
            changedSyms1' = HM.insert i1 newSymId1 changedSyms1
            changedSyms2' = HM.insert i2 newSymId2 changedSyms2
            mergedExprObj = E.ExprObj (mergeExpr newId (Var newSymId1) (Var newSymId2))
        in ((changedSyms1', changedSyms2', ngen''), mergedExprObj)

updatePCs :: Context t -> HM.HashMap Id Id -> HM.HashMap Id Id -> Context t
updatePCs ctxt@(Context { s1_ = s1@(State {path_conds = pc1}), s2_ = s2@(State {path_conds = pc2}) }) changedSyms1 changedSyms2 =
    let pc1' = subIdNamesPCs pc1 changedSyms1 -- update PathConds with new SymbolicIds from merging the expr_env
        pc2' = subIdNamesPCs pc2 changedSyms2
        s1' = s1 {path_conds = pc1'}
        s2' = s2 {path_conds = pc2'}
    in ctxt {s1_ = s1', s2_ = s2'}

updateSymbolicIds :: Context t -> HM.HashMap Id Id -> HM.HashMap Id Id -> Context t
updateSymbolicIds ctxt@(Context { s1_ = s1@(State {symbolic_ids = syms1}), s2_ = s2@(State {symbolic_ids = syms2}) }) changedSyms1 changedSyms2 =
    let
        oldSyms1 = HM.keys changedSyms1
        newSyms1 = HM.elems changedSyms1
        syms1' = HS.union (HS.fromList newSyms1) $ HS.difference syms1 (HS.fromList oldSyms1)
        oldSyms2 = HM.keys changedSyms2
        newSyms2 = HM.elems changedSyms2
        syms2' = HS.union (HS.fromList newSyms2) $ HS.difference syms2 (HS.fromList oldSyms2)
    in ctxt { s1_ = s1 { symbolic_ids = syms1' }, s2_ = s2 { symbolic_ids = syms2' } }

-- | Simpler version of mergePathConds, may not be very efficient for large numbers of PCs, but suffices for simple cases
mergePathCondsSimple :: Context t -> PathConds
mergePathCondsSimple (Context {s1_ = (State {path_conds = pc1, known_values = kv}), s2_ = (State {path_conds = pc2}), newId_ = newId, newPCs_ = newPCs}) =
    let pc1HS = HS.fromList (PC.toList pc1)
        pc2HS = HS.fromList (PC.toList pc2)
        common = HS.toList $ HS.intersection pc1HS pc2HS
        pc1Only = HS.toList $ HS.difference pc1HS pc2HS
        pc2Only = HS.toList $ HS.difference pc2HS pc1HS
        pc1Only' = map (\pc -> AssumePC newId 1 pc) pc1Only
        pc2Only' = map (\pc -> AssumePC newId 2 pc) pc2Only
        mergedPC = PC.fromList common
        mergedPC' = foldr PC.insert mergedPC (pc1Only' ++ pc2Only')
        mergedPC'' = PC.insert (ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var newId) 1) (mkEqIntExpr kv (Var newId) 2)) True) mergedPC'
        mergedPC''' = foldr PC.insert mergedPC'' newPCs
    in mergedPC'''

-- | Does not always work if 2 top level AssumePCs both impose constraints on the same Name -> resulting in model generating conflicting values
-- and one being arbitrarily chosen over the other
mergePathConds :: Context t -> PathConds
mergePathConds (Context {s1_ = (State {path_conds = pc1, known_values = kv}), s2_ = (State {path_conds = pc2}), newId_ = newId, newPCs_ = newPCs}) =
    -- If a key exists in both maps, then the respective values are combined and inserted into pc1_map'. 
    -- Else, all other values in pc1_map are added to pc1_map' as it is.
    -- pc2_map' will only contain values whose keys are not present in pc1_map
    let
        pc2_map = PC.toMap pc2
        pc1_map = PC.toMap pc1
        ((pc2_map', newAssumePCs), pc1_map') = M.mapAccumWithKey (mergeMapEntries newId) (pc2_map, HS.empty) pc1_map
        combined_map = PC.PathConds (M.union pc2_map' pc1_map')
        -- Add the following expression to constrain the value newId can take to either 1/2 when solving
        combined_map' = PC.insert (ExtCond (mkOrExpr kv (mkEqIntExpr kv (Var newId) 1) (mkEqIntExpr kv (Var newId) 2)) True) combined_map
    in L.foldr PC.insert (HS.foldr PC.insert combined_map' newAssumePCs) newPCs

-- A map and key,value pair are passed as arguments to the function. If the key exists in the map, then both values
-- are combined and the entry deleted from the map. Else the map and value are simply returned as it is.
mergeMapEntries :: Id -> (M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond)
                -> (Maybe Name)
                -> (HS.HashSet PC.PathCond, HS.HashSet Name)
                -> ((M.Map (Maybe Name) (HS.HashSet PathCond, HS.HashSet Name), HS.HashSet PC.PathCond), (HS.HashSet PC.PathCond, HS.HashSet Name))
mergeMapEntries newId (pc2_map, newAssumePCs) key (hs1, ns1) =
    case M.lookup key pc2_map of
        Just (hs2, ns2) -> ((pc2_map', newAssumePCs'), (mergedHS, mergedNS))
            where
                pc2_map' = M.delete key pc2_map
                (mergedHS, unmergedPCs) = mergeHashSets newId hs1 hs2
                mergedNS = HS.union ns1 ns2 -- names should still be the same even though some PCs are wrapped in AssumePCs and moved to different node
                newAssumePCs' = HS.union newAssumePCs unmergedPCs
        Nothing -> ((pc2_map, newAssumePCs), (hs1, ns1))

-- Any PathCond present in both HashSets is added as it is to the new HashSet.
-- A PathCond present in only 1 HashSet is changed to the form 'AssumePC (x == _) PathCond' and added to the new HashSet
mergeHashSets :: Id -> (HS.HashSet PathCond) -> (HS.HashSet PathCond) -> (HS.HashSet PathCond, HS.HashSet PathCond)
mergeHashSets newId hs1 hs2 = (common, unmergedPCs)
    where
        common = HS.intersection hs1 hs2
        hs1Minus2 = HS.difference hs1 hs2
        hs2Minus1 = HS.difference hs2 hs1
        hs1Minus2' = HS.map (\pc -> AssumePC newId 1 pc) hs1Minus2
        hs2Minus1' = HS.map (\pc -> AssumePC newId 2 pc) hs2Minus1
        unmergedPCs = HS.union hs1Minus2' hs2Minus1'

-- | @`changedSyms` is list of tuples, w/ each tuple representing the old symbolic Id and the new replacement Id. @`subIdsPCs` substitutes all
-- occurrences of the old symbolic Ids' Names in the PathConds with the Name of the corresponding new Id. This assumes Old and New Id have the same type
subIdNamesPCs :: PathConds -> HM.HashMap Id Id -> PathConds
subIdNamesPCs pcs changedSyms =
    let changedSymsNames = HM.foldrWithKey (\k v hm -> HM.insert (idName k) (idName v) hm) HM.empty changedSyms
    in renames changedSymsNames pcs
