{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.Rules ( module G2.Execution.RuleTypes
                          , Sharing (..)
                          , stdReduce
                          , evalVarSharing
                          , evalApp
                          , evalLam
                          , retLam
                          , evalLet
                          , evalCase
                          , evalCast
                          , evalTick
                          , evalNonDet
                          , evalSymGen
                          , evalAssume
                          , evalAssert
                          , isExecValueForm ) where

import G2.Config.Config
import G2.Execution.NewPC
import G2.Execution.NormalForms
import G2.Execution.PrimitiveEval
import G2.Execution.Merging.StateMerging
import G2.Execution.RuleTypes
import qualified G2.Execution.Merging.MergingHelpers as SM
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import G2.Preprocessing.NameCleaner
import G2.Solver hiding (Assert)

import Control.Monad.Extra
import Data.Maybe

import qualified Data.HashSet as HS
import qualified Data.HashMap.Lazy as HM
import qualified Data.List as L
import qualified Data.Map as M

import Control.Exception

import Debug.Trace

stdReduce :: (Solver solver, Simplifier simplifier) => Sharing -> Merging -> solver -> simplifier -> State t -> Bindings 
          -> IO (Rule, [(State t, ())], Bindings)
stdReduce sharing merging solver simplifier s b@(Bindings { name_gen = ng, last_merge_point = mp }) = do
    (r, s', ng', mp') <- stdReduce' sharing merging solver simplifier s ng mp
    let s'' = map (\ss -> ss { rules = r:rules ss }) s'
    return (r, zip s'' (repeat ()), b { name_gen = ng', last_merge_point = mp' })

stdReduce' :: (Solver solver, Simplifier simplifier) => Sharing -> Merging -> solver -> simplifier -> State t -> NameGen -> MergePoint -> IO (Rule, [State t], NameGen, MergePoint)
stdReduce' share mergeStates solver simplifier s@(State { curr_expr = CurrExpr Evaluate ce }) ng mp
    | Var i  <- ce
    , share == Sharing = returnWithMP $ evalVarSharing s ng i
    | Var i <- ce
    , share == NoSharing = returnWithMP $ evalVarNoSharing s ng i
    | App e1 e2 <- ce = returnWithMP $ evalApp s ng e1 e2
    | Let b e <- ce = returnWithMP $ evalLet s ng b e
    | Case e i a <- ce = do
        let (r, xs, ng', mp') = evalCase mergeStates s ng mp e i a
        xs' <- mapMaybeM (reduceNewPC solver simplifier) xs
        return (r, xs', ng', mp')
    | Cast e c <- ce = returnWithMP $ evalCast s ng e c
    | Tick t e <- ce = returnWithMP $ evalTick s ng t e
    | NonDet es <- ce = returnWithMP $ evalNonDet s ng es
    | SymGen t <- ce = returnWithMP $ evalSymGen s ng t
    | Assume fc e1 e2 <- ce = returnWithMP $ evalAssume s ng fc e1 e2
    | Assert fc e1 e2 <- ce = returnWithMP $ evalAssert s ng fc e1 e2
    | otherwise = returnWithMP (RuleReturn, [s { curr_expr = CurrExpr Return ce }], ng)
        where
            returnWithMP (r_, s_, ng_) = return (r_, s_, ng_, mp)
stdReduce' _ _ solver simplifier s@(State { curr_expr = CurrExpr Return ce
                                 , exec_stack = stck }) ng mp
    | isError ce
    , Just (AssertFrame is _, stck') <- S.pop stck =
        returnWithMP (RuleError, [s { exec_stack = stck'
                              , true_assert = True
                              , assert_ids = is }], ng)
    | Just (UpdateFrame n, stck') <- frstck = returnWithMP $ retUpdateFrame s ng n stck'
    | isError ce
    , Just (_, stck') <- S.pop stck = returnWithMP (RuleError, [s { exec_stack = stck' }], ng)
    | Just (MergePtFrame i, stck') <- frstck = do
        returnWithMP (RuleHitMergePt, [s {exec_stack = stck'}], ng)
    | Just rs <- retReplaceSymbFunc s ng ce = returnWithMP rs
    | Just (CaseFrame i a, stck') <- frstck = returnWithMP $ retCaseFrame s ng ce i a stck'
    | Just (CastFrame c, stck') <- frstck = returnWithMP $ retCastFrame s ng ce c stck'
    | Lam u i e <- ce = returnWithMP $ retLam s ng u i e
    | Just (ApplyFrame e, stck') <- S.pop stck = returnWithMP $ retApplyFrame s ng ce e stck'
    | Just (AssumeFrame e, stck') <- frstck = do
        let (r, xs, ng') = retAssumeFrame s ng ce e stck'
        xs' <- mapMaybeM (reduceNewPC solver simplifier) xs
        returnWithMP (r, xs', ng')
    | Just (AssertFrame ais e, stck') <- frstck = do
        let (r, xs, ng') = retAssertFrame s ng ce ais e stck'
        xs' <- mapMaybeM (reduceNewPC solver simplifier) xs
        returnWithMP (r, xs', ng')
    | Just (CurrExprFrame act e, stck') <- frstck = do
        let (r, xs) = retCurrExpr s ce act e stck'
        xs' <- mapMaybeM (reduceNewPC solver simplifier) xs
        returnWithMP (r, xs', ng)
    | Nothing <- frstck = returnWithMP (RuleIdentity, [s], ng)
    | otherwise = error $ "stdReduce': Unknown Expr" ++ show ce ++ show (S.pop stck)
        where
            frstck = S.pop stck

            isError (Prim Error _) = True
            isError (Prim Undefined _) = True
            isError _ = False

            returnWithMP (r_, s_, ng_) = return (r_, s_, ng_, mp)

evalVarSharing :: State t -> NameGen -> Id -> (Rule, [State t], NameGen)
evalVarSharing s@(State { expr_env = eenv
                        , exec_stack = stck })
               ng i
    | E.isSymbolic (idName i) eenv =
        (RuleEvalVal, [s { curr_expr = CurrExpr Return (Var i)}], ng)
    -- If the target in our environment is already a value form, we do not
    -- need to push additional redirects for updating later on.
    -- If our variable is not in value form, we first push the
    -- current name of the variable onto the stack and evaluate the
    -- expression that it points to. After the evaluation,
    -- we pop the stack to add a redirection pointer into the heap.
    | Just e' <- e
    , isExprValueForm eenv e' =
      ( RuleEvalVarVal (idName i), [s { curr_expr = CurrExpr Evaluate e' }], ng)
    | Just e' <- e = -- e' is NOT in SWHNF
      ( RuleEvalVarNonVal (idName i)
      , [s { curr_expr = CurrExpr Evaluate e'
           , exec_stack = S.push (UpdateFrame (idName i)) stck }]
      , ng)
    | otherwise = error  $ "evalVar: bad input." ++ show i
    where
        e = E.lookup (idName i) eenv

evalVarNoSharing :: State t -> NameGen -> Id -> (Rule, [State t], NameGen)
evalVarNoSharing s@(State { expr_env = eenv })
                 ng i
    | E.isSymbolic (idName i) eenv =
        (RuleEvalVal, [s { curr_expr = CurrExpr Return (Var i)}], ng)
    | Just e <- E.lookup (idName i) eenv =
        (RuleEvalVarNonVal (idName i), [s { curr_expr = CurrExpr Evaluate e }], ng)
    | otherwise = error  $ "evalVar: bad input." ++ show i

-- | If we have a primitive operator, we are at a point where either:
--    (1) We can concretely evaluate the operator, or
--    (2) We have a symbolic value, and no evaluation is possible, so we return
-- If we do not have a primitive operator, we go into the center of the apps,
-- to evaluate the function call
evalApp :: State t -> NameGen -> Expr -> Expr -> (Rule, [State t], NameGen)
evalApp s@(State { expr_env = eenv
                 , known_values = kv
                 , exec_stack = stck })
        ng e1 e2
    | (App (Prim BindFunc _) v) <- e1
    , Var i1 <- findSym v
    , v2 <- e2 =
        ( RuleBind
        , [s { expr_env = E.insert (idName i1) v2 eenv
             , curr_expr = CurrExpr Return (mkTrue kv) }]
        , ng)

    | ac@(Prim Error _) <- appCenter e1 = (RuleError, [s { curr_expr = CurrExpr Return ac }], ng)
    | isExprValueForm eenv (App e1 e2) =
        ( RuleReturnAppSWHNF
        , [s { curr_expr = CurrExpr Return (App e1 e2) }]
        , ng)
    | (Prim prim ty):ar <- unApp (App e1 e2) = 
        let
            ar' = map (lookupForPrim eenv) ar
            appP = mkApp (Prim prim ty : ar')
            -- replace any Case Exprs in appP with a Symbolic variable to ensure the Expr is in Symbolic Weak Head Normal Form
            (s', ng', appP') = SM.replaceCaseWSym s ng appP
            exP = evalPrims kv appP'
        in
        ( RuleEvalPrimToNorm
        , [s' { curr_expr = CurrExpr Return exP }]
        , ng')
    | otherwise =
        let
            frame = ApplyFrame e2
            stck' = S.push frame stck
        in
        ( RuleEvalApp e2
        , [s { curr_expr = CurrExpr Evaluate e1
             , exec_stack = stck' }]
        , ng)
    where
        findSym v@(Var (Id n _))
          | E.isSymbolic n eenv = v
          | Just e <- E.lookup n eenv = findSym e
        findSym _ = error "findSym: No symbolic variable"

lookupForPrim :: ExprEnv -> Expr -> Expr
lookupForPrim eenv v@(Var (Id _ _)) = repeatedLookup eenv v
lookupForPrim eenv (App e e') = App (lookupForPrim eenv e) (lookupForPrim eenv e')
lookupForPrim _ e = e

repeatedLookup :: ExprEnv -> Expr -> Expr
repeatedLookup eenv v@(Var (Id n _))
    | E.isSymbolic n eenv = v
    | otherwise = 
        case E.lookup n eenv of
          Just v'@(Var _) -> repeatedLookup eenv v'
          Just e -> e
          Nothing -> v
repeatedLookup _ e = e

evalLam :: State t -> LamUse -> Id -> Expr -> (Rule, [State t])
evalLam = undefined

retLam :: State t -> NameGen -> LamUse -> Id -> Expr -> (Rule, [State t], NameGen)
retLam s@(State { expr_env = eenv
                , exec_stack = stck })
       ng u i e
    | TypeL <- u
    , Just (ApplyFrame tf, stck') <- S.pop stck =
        case traceType eenv tf of
        Just t ->
            let
                e' = retypeOutsideTyForAll i t e

                (eenv', e'', ng', news) = liftBind i (Type t) eenv e' ng
            in
            ( RuleReturnEApplyLamType [news]
            , [s { expr_env = eenv'
                 , curr_expr = CurrExpr Evaluate e''
                 , exec_stack = stck' }]
            , ng')
        Nothing -> error $ "retLam: Bad type\ni = " ++ show i ++ "\nstck = " ++ show (S.pop stck) 
    | TermL <- u
    , Just (ApplyFrame ae, stck') <- S.pop stck =
        let
            (eenv', e', ng', news) = liftBind i ae eenv e ng
        in
        ( RuleReturnEApplyLamExpr [news]
        , [s { expr_env = eenv'
             , curr_expr = CurrExpr Evaluate e'
             , exec_stack = stck' }]
        ,ng')
    | otherwise = error "retLam: Bad type"

traceType :: E.ExprEnv -> Expr -> Maybe Type
traceType _ (Type t) = Just t
traceType eenv (Var (Id n _)) = traceType eenv =<< E.lookup n eenv
traceType _ _ = Nothing

evalLet :: State t -> NameGen -> Binds -> Expr -> (Rule, [State t], NameGen)
evalLet s@(State { expr_env = eenv }) 
        ng binds e =
    let
        (binds_lhs, binds_rhs) = unzip binds

        olds = map idName binds_lhs
        (news, ng') = freshSeededNames olds ng

        e' = renames (HM.fromList $ zip olds news) e
        binds_rhs' = renames (HM.fromList $ zip olds news) binds_rhs

        eenv' = E.insertExprs (zip news binds_rhs') eenv
    in
    (RuleEvalLet news, [s { expr_env = eenv'
                          , curr_expr = CurrExpr Evaluate e'}]
                     , ng')

-- | Handle the Case forms of Evaluate.
evalCase :: Merging -> State t -> NameGen -> MergePoint -> Expr -> Id -> [Alt] -> (Rule, [NewPC t], NameGen, MergePoint)
evalCase mergeStates s@(State { expr_env = eenv
                       , exec_stack = stck })
         ng mp mexpr bind alts
  -- Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | (Lit lit) <- unsafeElimOuterCast mexpr
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
      let 
          binds = [(bind, Lit lit)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseLit
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng, mp)

  -- Is the current expression able to match a data consturctor based `Alt`?
  -- If so, then we bind all the parameters to the appropriate arguments and
  -- proceed with the evaluation of the `Alt`'s expression. We also make sure
  -- to perform the cvar binding.
  -- We unwrap the outermost cast from the mexpr.  It must be being cast
  -- to the DataCon type, so this is safe, and needed for our pattern matching.
  -- We do not want to remove casting from any of the arguments since this could
  -- mess up there types later
  | (Data dcon):ar <- unApp $ exprInCasts mexpr
  , (DataCon _ _) <- dcon
  , ar' <- removeTypes ar eenv
  , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
  , length params == length ar' =
      let
          dbind = [(bind, mexpr)]
          expr' = liftCaseBinds dbind expr
          pbinds = zip params ar'
          (eenv', expr'', ng', news) = liftBinds pbinds eenv expr' ng
      in 
         ( RuleEvalCaseData news
         , [newPCEmpty $ s { expr_env = eenv'
                           , curr_expr = CurrExpr Evaluate expr''}] 
         , ng'
         , mp)

  -- We are not able to match any constructor but don't have a symbolic variable?
  -- We hit a DEFAULT instead.
  -- We perform the cvar binding and proceed with the alt
  -- expression.
  | e:_ <- unApp $ unsafeElimOuterCast mexpr
  , isData e
      || isLit e
      || isLam e
      || (case e of Var i@(Id n _) -> E.isSymbolic n eenv && hasFuncType i; _ -> False)
  , (Alt _ expr):_ <- matchDefaultAlts alts =
      let 
          binds = [(bind, mexpr)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseDefault
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng, mp)

  | isSMNF eenv mexpr
  , Case _ _ _ <- mexpr
  , Merging <- mergeStates =
    -- get list of matches w/ respective assumption
    let choices = getChoices s mexpr
        dalts = [a | a @ (Alt (DataAlt _ _) _) <- alts]
        defs = [a | a @ (Alt Default _) <- alts]
        -- for each (DataAlt dcon params) match relevant choices that are Apps with a (Data dcon') center
        (daltMatches, choices') = matchDataAltsSMNF eenv dalts choices
         -- Match all unmatched Apps with a (Data _) center
        defMatches = matchDefaults defs choices'

        -- split into multiple states on the various Alts appropriately
        (ng', dsts_cs) = handleDaltMatches s bind ng daltMatches
        def_sts = handleDefMatches s defMatches bind

        newPCs = def_sts ++ dsts_cs

        mp' = freshMergePoint mp
        newPCs' = map (addMergePt mp') newPCs
    in (RuleEvalCaseSym bind, newPCs', ng', mp') -- TODO: new rule

  -- If we are pointing to something in expr value form, that is not addressed
  -- by some previous case, we handle it by branching on every `Alt`, and adding
  -- path constraints.
  | isExprValueForm eenv mexpr
  , dalts <- dataAlts alts
  , lalts <- litAlts alts
  , defs <- defaultAlts alts
  , (length dalts + length lalts + length defs) > 0 =
    let
        (cast, expr) = case mexpr of
            (Cast e c) -> (Just c, e)
            _ -> (Nothing, mexpr)

        (dsts_cs, ng') = case unApp $ unsafeElimOuterCast expr of
            (Var i@(Id _ _)):_ -> concretizeVarExpr s ng i bind dalts cast
            (Prim _ _):_ -> createExtConds s ng expr bind dalts
            (Lit _):_ -> ([], ng)
            (Data _):_ -> ([], ng)
            _ -> error $ "unmatched expr" ++ show (unApp $ unsafeElimOuterCast mexpr)
            
        lsts_cs = liftSymLitAlt s mexpr bind lalts
        (def_sts, ng'') = liftSymDefAlt s ng' mexpr bind alts
        newPCs = dsts_cs ++ lsts_cs ++ def_sts

        mp' = freshMergePoint mp
        newPCs' = map (addMergePt mp') newPCs
      in
      (RuleEvalCaseSym bind, newPCs', ng'', mp')

  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
  -- is only done when the matching expression is NOT in value form. Value
  -- forms should be handled by other RuleEvalCase* rules.
  | not (isExprValueForm eenv mexpr) =
      let frame = CaseFrame bind alts
      in ( RuleEvalCaseNonVal
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate mexpr
                           , exec_stack = S.push frame stck }], ng, mp)

  | otherwise = error $ "reduceCase: bad case passed in\n" ++ show mexpr ++ "\n" ++ show alts

-- | Remove everything from an [Expr] that are actually Types.
removeTypes :: [Expr] -> E.ExprEnv -> [Expr]
removeTypes ((Type _):es) eenv = removeTypes es eenv
removeTypes (v@(Var _):es) eenv = case repeatedLookup eenv v of
    (Type _) -> removeTypes es eenv
    -- Just v@(Var (Id n' _)) -> removeTypes (v:es) eenv 
    _ -> v : removeTypes es eenv
removeTypes (e:es) eenv = e : removeTypes es eenv
removeTypes [] _ = []

-- | DEFAULT `Alt`s.
matchDefaultAlts :: [Alt] -> [Alt]
matchDefaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts (DataCon n _) alts =
  [a | a @ (Alt (DataAlt (DataCon n' _) _) _) <- alts, n == n']

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

liftCaseBinds :: [(Id, Expr)] -> Expr -> Expr
liftCaseBinds [] expr = expr
liftCaseBinds ((b, e):xs) expr = liftCaseBinds xs $ replaceVar (idName b) e expr

-- | `DataCon` `Alt`s.
dataAlts :: [Alt] -> [(DataCon, [Id], Expr)]
dataAlts alts = [(dcon, ps, aexpr) | Alt (DataAlt dcon ps) aexpr <- alts]

-- | `Lit` `Alt`s.
litAlts :: [Alt] -> [(Lit, Expr)]
litAlts alts = [(lit, aexpr) | Alt (LitAlt lit) aexpr <- alts]

-- | DEFAULT `Alt`s.
defaultAlts :: [Alt] -> [Alt]
defaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Lift positive datacon `State`s from symbolic alt matching. This in
-- part involves erasing all of the parameters from the environment by rename
-- their occurrence in the aexpr to something fresh.
concretizeVarExpr :: State t -> NameGen -> Id -> Id -> [(DataCon, [Id], Expr)] -> Maybe Coercion -> ([NewPC t], NameGen)
concretizeVarExpr _ ng _ _ [] _ = ([], ng)
concretizeVarExpr s ng mexpr_id cvar (x:xs) maybeC =
        (x':newPCs, ng'') 
    where
        (x', ng') = concretizeVarExpr' s ng mexpr_id cvar x maybeC
        (newPCs, ng'') = concretizeVarExpr s ng' mexpr_id cvar xs maybeC

concretizeVarExpr' :: State t -> NameGen -> Id -> Id -> (DataCon, [Id], Expr) -> Maybe Coercion -> (NewPC t, NameGen)
concretizeVarExpr' s@(State {expr_env = eenv, type_env = tenv})
                ngen mexpr_id cvar (dcon, params, aexpr) maybeC =
          (NewPC { state =  s { expr_env = eenv''
                              , curr_expr = CurrExpr Evaluate aexpr''}
                 -- It is VERY important that we insert the mexpr_id in `concretized`
                 -- This forces reduceNewPC to check that the concretized data constructor does
                 -- not violate any path constraints from default cases. 
                 , new_pcs = []
                 , concretized = [mexpr_id]
                 }, ngen')
  where
    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params
    clean_olds = map cleanName olds

    -- [ChildrenNames]
    -- Optimization
    -- We use the same names repeatedly for the children of the same ADT
    -- Haskell is purely functional, so this is OK!  The children can't change
    -- Then, in the constraint solver, we can consider fewer constraints at once
    -- (see note [AltCond] in Language/PathConds.hs) 
    mexpr_n = idName mexpr_id
    (news, ngen') = childrenNames mexpr_n clean_olds ngen

    --Update the expr environment
    newIds = map (\(Id _ t, n) -> Id n t) (zip params news)
    eenv' = foldr E.insertSymbolic eenv newIds

    (dcon', aexpr') = renameExprs (zip olds news) (Data dcon, aexpr)

    newparams = map (uncurry Id) $ zip news (map typeOf params)
    dConArgs = (map (Var) newparams)
    -- Get list of Types to concretize polymorphic data constructor and concatenate with other arguments
    mexpr_t = typeOf mexpr_id
    type_ars = mexprTyToExpr mexpr_t tenv
    exprs = [dcon'] ++ type_ars ++ dConArgs

    -- Apply list of types (if present) and DataCon children to DataCon
    dcon'' = mkApp exprs

    -- Apply cast, in opposite direction of unsafeElimOuterCast
    dcon''' = case maybeC of 
                (Just (t1 :~ t2)) -> Cast dcon'' (t2 :~ t1)
                Nothing -> dcon''

    -- concretizes the mexpr to have same form as the DataCon specified
    eenv'' = E.insert mexpr_n dcon''' eenv' 

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, (Var mexpr_id))]
    aexpr'' = liftCaseBinds binds aexpr'

    
-- | Given the Type of the matched Expr, looks for Type in the TypeEnv, and returns Expr level representation of the Type
mexprTyToExpr :: Type -> TypeEnv -> [Expr]
mexprTyToExpr mexpr_t = reverse . mexprTyToExpr' mexpr_t

mexprTyToExpr' :: Type -> TypeEnv -> [Expr]
mexprTyToExpr' mexpr_t tenv 
    -- special case for NewTyCon, involves looking up tyVars and binding them to concrete types specified by mexpr_t
    | Just (algDataTy, bindings) <- getAlgDataTy mexpr_t tenv     
    , (isNewTyCon algDataTy) = dconTyToExpr (data_con algDataTy) bindings
    | otherwise = typeToExpr mexpr_t

-- | Given a DataCon, and an (Id, Type) mapping, returns list of Expression level Type Arguments to DataCon
dconTyToExpr :: DataCon -> [(Id, Type)] -> [Expr]
dconTyToExpr (DataCon _ t) bindings =
    case (getTyApps t) of
        (Just tApps) -> tyAppsToExpr tApps bindings
        Nothing -> []

createExtConds :: State t -> NameGen -> Expr -> Id -> [(DataCon, [Id], Expr)] -> ([NewPC t], NameGen)
createExtConds _ ng _ _ [] = ([], ng)
createExtConds s ng mexpr cvar (x:xs) = 
        (x':newPCs, ng'') 
    where
        (x', ng') = createExtCond s ng mexpr cvar x
        (newPCs, ng'') = createExtConds s ng' mexpr cvar xs

createExtCond :: State t -> NameGen -> Expr -> Id -> (DataCon, [Id], Expr) -> (NewPC t, NameGen)
createExtCond s ngen mexpr cvar (dcon, _, aexpr) =
        (NewPC { state = res, new_pcs = [cond] , concretized = []}, ngen)
  where
    -- Get the Bool value specified by the matching DataCon
    -- Throws an error if dcon is not a Bool Data Constructor
    boolValue = getBoolFromDataCon (known_values s) dcon
    cond = ExtCond mexpr boolValue

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, mexpr)]
    aexpr' = liftCaseBinds binds aexpr
    res = s {curr_expr = CurrExpr Evaluate aexpr'}

getBoolFromDataCon :: KnownValues -> DataCon -> Bool
getBoolFromDataCon kv dcon
    | (DataCon dconName dconType) <- dcon
    , dconType == (tyBool kv)
    , dconName == (KV.dcTrue kv) = True
    | (DataCon dconName dconType) <- dcon
    , dconType == (tyBool kv)
    , dconName == (KV.dcFalse kv) = False
    | otherwise = error $ "getBoolFromDataCon: invalid DataCon passed in\n" ++ show dcon ++ "\n"

liftSymLitAlt :: State t -> Expr -> Id -> [(Lit, Expr)] -> [NewPC t]
liftSymLitAlt s mexpr cvar = map (liftSymLitAlt' s mexpr cvar)

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt' :: State t -> Expr -> Id -> (Lit, Expr) -> NewPC t
liftSymLitAlt' s mexpr cvar (lit, aexpr) =
    NewPC { state = res, new_pcs = [cond] , concretized = [] }
  where
    -- Condition that was matched.
    cond = AltCond lit mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    aexpr' = liftCaseBinds binds aexpr
    res = s { curr_expr = CurrExpr Evaluate aexpr' }

----------------------------------------------------
-- Default Alternatives

liftSymDefAlt :: State t -> NameGen -> Expr ->  Id -> [Alt] -> ([NewPC t], NameGen)
liftSymDefAlt s ng mexpr cvar as =
    let
        match = defAltExpr as
    in
    case match of
        Just aexpr -> liftSymDefAlt' s ng mexpr aexpr cvar as
        _ -> ([], ng)

-- | Concretize Symbolic variable to Case Expr on its possible Data Constructors
liftSymDefAlt' :: State t -> NameGen -> Expr -> Expr -> Id -> [Alt] -> ([NewPC t], NameGen)
liftSymDefAlt' s@(State {type_env = tenv}) ng mexpr aexpr cvar alts
    | (Var i):_ <- unApp $ unsafeElimOuterCast mexpr
    , isADTType (typeOf i)
    , (Var i'):_ <- unApp $ exprInCasts mexpr = -- Id with original Type
        let (adt, bi) = fromJust $ getCastedAlgDataTy (typeOf i) tenv
            maybeC = case mexpr of
                (Cast _ c) -> Just c
                _ -> Nothing
            dcs = dataCon adt
            badDCs = mapMaybe (\alt -> case alt of
                (Alt (DataAlt dc _) _) -> Just dc
                _ -> Nothing) alts
            dcs' = L.deleteFirstsBy (\(DataCon n1 _) (DataCon n2 _) -> n1 == n2) dcs badDCs

            (newId, ng') = freshId TyLitInt ng

            ((s', ng''), dcs'') = L.mapAccumL (concretizeSym bi maybeC) (s, ng') dcs'

            mexpr' = createCaseExpr newId dcs''
            binds = [(cvar, mexpr')]
            aexpr' = liftCaseBinds binds aexpr

            -- add PC restricting range of values for newSymId
            newSymConstraint = restrictSymVal (known_values s') 1 (toInteger $ length dcs'') newId

            eenv' = E.insert (idName i') mexpr' (expr_env s')
            s'' = s' { curr_expr = CurrExpr Evaluate aexpr'
                     , expr_env = eenv'}
        in
        ([NewPC { state = s'', new_pcs = [newSymConstraint], concretized = [] }], ng'')
    | Prim _ _:_ <- unApp mexpr = (liftSymDefAlt'' s mexpr aexpr cvar alts, ng)
    | isPrimType (typeOf mexpr) = (liftSymDefAlt'' s mexpr aexpr cvar alts, ng)
    | otherwise = error $ "liftSymDefAlt': unhandled Expr" ++ "\n" ++ show mexpr

liftSymDefAlt'' :: State t -> Expr -> Expr -> Id -> [Alt] -> [NewPC t]
liftSymDefAlt'' s mexpr aexpr cvar as =
    let
        conds = mapMaybe (liftSymDefAltPCs (known_values s) mexpr) (map altMatch as)

        binds = [(cvar, mexpr)]
        aexpr' = liftCaseBinds binds aexpr
    in
    [NewPC { state = s { curr_expr = CurrExpr Evaluate aexpr' }
           , new_pcs = conds
           , concretized = [] }]

liftSymDefAltPCs :: KnownValues -> Expr -> AltMatch -> Maybe PathCond
liftSymDefAltPCs kv mexpr (DataAlt dc _) = -- Only DataAlts would be True/False
    let boolVal = getBoolFromDataCon kv dc
    in case boolVal of
        True -> Just $ ExtCond mexpr False
        False -> Just $ ExtCond mexpr True
liftSymDefAltPCs _ mexpr (LitAlt lit) = Just $ AltCond lit mexpr False
liftSymDefAltPCs _ _ Default = Nothing

-- Insert MergePtFrame into stack and increment count of unmerged cases at the case specified by `i`
addMergePt :: MergePoint -> NewPC t -> NewPC t
addMergePt mp p@(NewPC {state = s@(State { exec_stack = stk })}) =
    let stk' = S.push (MergePtFrame mp) stk in 
    p { state = s { exec_stack = stk' } }

-----------------------------------------------------------------------------
--  Helper functions to deal with Case Expr in Symbolic Merged Normal Form --
-----------------------------------------------------------------------------
type Cond = (Id, Integer) -- TODO: change name
type Condition = Expr

data Match = Constructor (Expr, [Condition])
           | Defaults [(Expr, [Condition])] deriving (Show)

-- | Given a `Case` expr in SMNF, returns a list of pairs of the Exprs and their associated conditions in Expr form
-- e.g. getChoices Case (Var x) of 1 -> A, 2 -> C) = [(A, [(x == 1)]), (C, [(x == 2)])]
getChoices :: State t -> Expr -> [(Expr, [Condition])]
getChoices (State {known_values = kv}) e@(Case _ _ _) =
    let choices = getChoices' e -- [(Expr, Cond)]
    in map (\(expr, (i, num)) ->
            let assum = mkEqExpr kv (Var i) (Lit $ LitInt num)
            in (expr, [assum])) choices
getChoices  _ e = [(e, [])]

getChoices' :: Expr -> [(Expr, Cond)]
getChoices' (Case (Var i) b (a:as))
    | (Alt (LitAlt (LitInt num)) e) <- a = (e, (i, num)):getChoices' (Case (Var i) b as)
    | otherwise = error "getTopLevelExprs called with Expr not from result of merging states. "
getChoices' _ = []

matchDataAltsSMNF :: E.ExprEnv -> [Alt] -> [(Expr, [Condition])] -> ([(Alt, Match)], [(Expr, [Condition])])
matchDataAltsSMNF eenv (alt:alts) choices =
    let
        (x', choices') = matchDataAlt eenv alt choices
        (xs, choices'') = matchDataAltsSMNF eenv alts choices'
    in case x' of --filter out alts without any matches
        Just match -> (match:xs, choices'')
        Nothing -> (xs, choices'')
matchDataAltsSMNF _ [] choices = ([], choices)

-- | If a choice `x` matches with the given `alt`, create a Match and delete the choice
matchDataAlt :: E.ExprEnv -> Alt -> [(Expr, [Condition])] -> (Maybe (Alt, Match), [(Expr, [Condition])])
matchDataAlt eenv alt (x@(mexpr, _):xs)
    | (Alt (DataAlt (DataCon n _) params) _) <- alt
    , (Data (DataCon n' _)):ar <- unApp $ exprInCasts mexpr
    , ar' <- removeTypes ar eenv
    , n == n'
    , length params == length ar' = (Just (alt, Constructor x), xs) -- delete x from choices
    | otherwise =
        let (match, choices') = matchDataAlt eenv alt xs
        in (match, x:choices')
matchDataAlt _ _ [] = (Nothing, [])

-- | If a choice in `choices` hits a Default `alt`, add to the Match
matchDefaults :: [Alt] -> [(Expr, [Condition])] -> Maybe (Alt, Match)
matchDefaults _ [] = Nothing
matchDefaults [] _ = Nothing
matchDefaults (alt:_) choices = Just (alt, Defaults choices) -- only need to look at 1 Default choice

handleDaltMatches :: State t -> Id -> NameGen -> [(Alt, Match)] -> (NameGen, [NewPC t])
handleDaltMatches s bind = L.mapAccumL (handleDaltMatch s bind)

handleDaltMatch :: State t -> Id -> NameGen -> (Alt, Match) -> (NameGen, NewPC t)
handleDaltMatch s@(State { expr_env = eenv }) bind ng (alt, match)
    | (Alt (DataAlt _ params) aexpr) <- alt
    , Constructor (mexpr, assums) <- match
    , (Data _):ar <- unApp $ exprInCasts mexpr
    , ar' <- removeTypes ar eenv =
        let dbind = [(bind, mexpr)]
            aexpr' = liftCaseBinds dbind aexpr
            pbinds = zip params ar'
            (eenv', aexpr'', ng', _) = liftBinds pbinds eenv aexpr' ng
            -- add PathConds representing the assumptions for that match
            assumsE = map (flip ExtCond True) assums
        in ( ng'
           , NewPC { state = s { expr_env = eenv'
                               , curr_expr = CurrExpr Evaluate aexpr''}
                   , new_pcs = assumsE
                   , concretized = [] })
    | otherwise = error $ "Alt is not a DataAlt"

handleDefMatches :: State t -> Maybe (Alt, Match) -> Id -> [NewPC t]
handleDefMatches s@(State { expr_env = eenv }) (Just (alt, Defaults matches)) bind
    -- Only 1 match, no need to insert Case expr
    | (Alt Default aexpr) <- alt
    , [(mexpr, assums)] <- matches =
        let
            binds = [(bind, mexpr)]
            aexpr' = liftCaseBinds binds aexpr
            s' = s {curr_expr = CurrExpr Evaluate aexpr'}
            conds = map (flip ExtCond True) assums
        in
        [NewPC {state = s', new_pcs = conds, concretized = []}]
    | otherwise = error $ "Alt is not a Default: " ++ show alt
handleDefMatches _ _ _ = []

--------------------------------------------------------------------------------------

defAltExpr :: [Alt] -> Maybe Expr
defAltExpr [] = Nothing
defAltExpr (Alt Default e:_) = Just e
defAltExpr (_:xs) = defAltExpr xs

----------------------------------------------------

evalCast :: State t -> NameGen -> Expr -> Coercion -> (Rule, [State t], NameGen)
evalCast s@(State { expr_env = eenv
                  , exec_stack = stck }) 
         ng e c@(t1 :~ t2)
    | Var init_i@(Id n _) <- e
    , E.isSymbolic n eenv
    , hasFuncType (PresType t2) && not (hasFuncType $ PresType t1) =
        let
            (i, ng') = freshId t2 ng
            new_e = Cast (Var i) (t2 :~ t1)
        in
        ( RuleOther
        , [s { expr_env = E.insertSymbolic i $ E.insert n new_e eenv
             , curr_expr = CurrExpr Return (Var i) }]
        , ng')
    | cast /= cast' =
        ( RuleEvalCastSplit
        , [ s { curr_expr = CurrExpr Evaluate $ simplifyCasts cast' }]
        , ng')
    | otherwise =
        ( RuleEvalCast
        , [s { curr_expr = CurrExpr Evaluate $ simplifyCasts e
             , exec_stack = S.push frame stck}]
        , ng)
    where
        cast = Cast e c
        (cast', ng') = splitCast ng cast
        frame = CastFrame c

evalTick :: State t -> NameGen -> Tickish -> Expr -> (Rule, [State t], NameGen)
evalTick s ng _ e = (RuleTick, [ s { curr_expr = CurrExpr Evaluate e }], ng)

evalNonDet :: State t -> NameGen -> [Expr] -> (Rule, [State t], NameGen)
evalNonDet s ng es =
    let
        s' = map (\e -> s { curr_expr = CurrExpr Evaluate e }) es
    in
    (RuleNonDet, s', ng)

evalSymGen :: State t -> NameGen -> Type -> (Rule, [State t], NameGen)
evalSymGen s@( State { expr_env = eenv }) 
           ng t =
    let
          (n, ng') = freshSeededString "symG" ng
          i = Id n t

          eenv' = E.insertSymbolic i eenv
    in
    (RuleSymGen, [s { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate (Var i) }]
                , ng')

evalAssume :: State t -> NameGen -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t], NameGen)
evalAssume s@(State { exec_stack = stck }) ng _ e1 e2 =
    let
        fr = AssumeFrame e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssume
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }]
    , ng)

evalAssert :: State t -> NameGen -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t], NameGen)
evalAssert s@(State { exec_stack = stck }) ng is e1 e2 =
    let
        fr = AssertFrame is e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssert
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }]
    , ng)

retUpdateFrame :: State t -> NameGen -> Name -> S.Stack Frame -> (Rule, [State t], NameGen)
retUpdateFrame s@(State { expr_env = eenv
                        , curr_expr = CurrExpr _ e}) ng un stck
    | Var i@(Id vn _) <- e =
       ( RuleReturnEUpdateVar un
       , [s { expr_env = E.redirect un vn eenv
            , curr_expr = CurrExpr Return (Var i)
            , exec_stack = stck }]
       , ng)
    | otherwise =
        ( RuleReturnEUpdateNonVar un
        , [s { expr_env = E.insert un e eenv
             , exec_stack = stck }]
        , ng)

retApplyFrame :: State t -> NameGen -> Expr -> Expr -> S.Stack Frame -> (Rule, [State t], NameGen)
retApplyFrame s@(State { expr_env = eenv }) ng e1 e2 stck'
    | Var (Id n _):_ <- unApp e1
    , E.isSymbolic n eenv = 
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Return (App e1 e2)
             , exec_stack = stck' }], ng)
    | otherwise =
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Evaluate (App e1 e2)
             , exec_stack = stck' }], ng)

retCaseFrame :: State t -> NameGen -> Expr -> Id -> [Alt] -> S.Stack Frame -> (Rule, [State t], NameGen)
retCaseFrame s b e i a stck =
    ( RuleReturnECase
    , [s { curr_expr = CurrExpr Evaluate (Case e i a)
         , exec_stack = stck }]
    , b)

retCastFrame :: State t -> NameGen -> Expr -> Coercion -> S.Stack Frame -> (Rule, [State t], NameGen)
retCastFrame s ng e c stck =
    ( RuleReturnCast
    , [s { curr_expr = CurrExpr Return $ simplifyCasts $ Cast e c
         , exec_stack = stck}]
    , ng)

retCurrExpr :: State t -> Expr -> CEAction -> CurrExpr -> S.Stack Frame -> (Rule, [NewPC t])
retCurrExpr s e1 AddPC e2 stck = 
    ( RuleReturnCurrExprFr
    , [NewPC { state = s { curr_expr = e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 True]
             , concretized = []}] )
retCurrExpr s e1 NoAction e2 stck = 
    ( RuleReturnCurrExprFr
    , [NewPC { state = s { curr_expr = e2
                         , exec_stack = stck}
             , new_pcs = []
             , concretized = []}] )

retAssumeFrame :: State t -> NameGen -> Expr -> Expr -> S.Stack Frame -> (Rule, [NewPC t], NameGen)
retAssumeFrame s@(State {known_values = kv
                        , type_env = tenv}) 
               ng e1 e2 stck =
    let
        -- Create a True Bool DataCon
        dalt = case (getDataCon tenv (KV.tyBool kv) (KV.dcTrue kv)) of
            Just dc -> [dc]
            _ -> []
        -- Special handling in case we just have a concrete DataCon, or a lone Var
        (newPCs, ng') = case unApp $ unsafeElimOuterCast e1 of
            [Data (DataCon dcn _)]
                | dcn == KV.dcFalse kv -> ([], ng)
                | dcn == KV.dcTrue kv ->
                    ( [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                                         , exec_stack = stck }
                             , new_pcs = []
                             , concretized = [] }]
                    , ng)
            (Var i@(Id _ _)):_ -> concretizeExprToBool s ng i dalt e2 stck
            _ -> ([addPathCond s e1 e2 True stck], ng)
    in
    (RuleReturnCAssume, newPCs, ng')

retAssertFrame :: State t -> NameGen -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> (Rule, [NewPC t], NameGen)
retAssertFrame s@(State {known_values = kv
                        , type_env = tenv}) 
               ng e1 ais e2 stck =
    let
        -- Create True and False Bool DataCons
        dalts = case getDataCons (KV.tyBool kv) tenv of
            Just dcs -> dcs
            _ -> []
        -- Special handling in case we just have a concrete DataCon, or a lone Var
        (newPCs, ng') = case unApp $ unsafeElimOuterCast e1 of
            [Data (DataCon dcn _)]
                | dcn == KV.dcFalse kv ->
                    ( [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                                         , exec_stack = stck
                                         , true_assert = True
                                         , assert_ids = ais } 
                             , new_pcs = []
                             , concretized = [] }]
                    , ng)
                | dcn == KV.dcTrue kv ->
                    ( [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                                         , exec_stack = stck }
                             , new_pcs = []
                             , concretized = [] }]
                    , ng)
            (Var i@(Id _ _)):_ -> concretizeExprToBool s ng i dalts e2 stck
            _ -> (addPathConds s e1 ais e2 stck, ng)
            
      in
      (RuleReturnCAssert, newPCs, ng')

concretizeExprToBool :: State t -> NameGen -> Id -> [DataCon] -> Expr -> S.Stack Frame -> ([NewPC t], NameGen)
concretizeExprToBool _ ng _ [] _ _ = ([], ng)
concretizeExprToBool s ng mexpr_id (x:xs) e2 stck = 
        (x':newPCs, ng'') 
    where
        (x', ng') = concretizeExprToBool' s ng mexpr_id x e2 stck
        (newPCs, ng'') = concretizeExprToBool s ng' mexpr_id xs e2 stck

concretizeExprToBool' :: State t -> NameGen -> Id -> DataCon -> Expr -> S.Stack Frame -> (NewPC t, NameGen)
concretizeExprToBool' s@(State {expr_env = eenv
                        , known_values = kv})
                ngen mexpr_id dcon@(DataCon dconName _) e2 stck = 
        (NewPC { state = s { expr_env = eenv'
                        , exec_stack = stck
                        , curr_expr = CurrExpr Evaluate e2
                        , true_assert = assertVal}
               , new_pcs = []
               , concretized = [] }
        , ngen)
    where
        mexpr_n = idName mexpr_id

        -- concretize the mexpr to the DataCon specified
        eenv' = E.insert mexpr_n (Data dcon) eenv

        assertVal = if (dconName == (KV.dcTrue kv))
                        then False
                        else True

addPathCond :: State t -> Expr -> Expr -> Bool -> S.Stack Frame -> NewPC t
addPathCond s e1 e2 boolVal stck =
    NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                       , exec_stack = stck }
          , new_pcs = SM.exprToPCs e1 boolVal
          , concretized = [] }

addPathConds :: State t -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> [NewPC t]
addPathConds s e1 ais e2 stck =
    let
        strue = addPathCond s e1 e2 True stck
        sfalse = addPathCond s e1 e2 False stck
        sfalse' = sfalse { state = (state sfalse) { true_assert = True
                                                  , assert_ids = ais } }
    in [strue, sfalse']

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, [Name])
liftBinds binds eenv expr ngen = (eenv', expr', ngen', news)
  where
    (bindsLHS, bindsRHS) = unzip binds

    olds = map (idName) bindsLHS
    (news, ngen') = freshSeededNames olds ngen

    olds_news = HM.fromList $ zip olds news
    expr' = renamesExprs olds_news expr

    eenv' = E.insertExprs (zip news bindsRHS) eenv

liftBind :: Id -> Expr -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, Name)
liftBind bindsLHS bindsRHS eenv expr ngen = (eenv', expr', ngen', new)
  where
    old = idName bindsLHS
    (new, ngen') = freshSeededName old ngen

    expr' = renameExpr old new expr

    eenv' = E.insert new bindsRHS eenv

-- If the expression is a symbolic higher order function application, replaces
-- it with a symbolic variable of the correct type.
-- A non reduced path constraint is added, to force solving for the symbolic
-- function later.
retReplaceSymbFunc :: State t -> NameGen -> Expr -> Maybe (Rule, [State t], NameGen)
retReplaceSymbFunc s@(State { expr_env = eenv
                            , known_values = kv
                            , type_classes = tc
                            , exec_stack = stck })
                   ng ce
    | Just (frm, _) <- S.pop stck
    , not (isApplyFrame frm)
    , (Var (Id f idt):_) <- unApp ce
    , E.isSymbolic f eenv
    , isTyFun idt
    , t <- typeOf ce
    , not (isTyFun t)
    , Just eq_tc <- concreteSatStructEq kv tc t =
        let
            (new_sym, ng') = freshSeededString "sym" ng
            new_sym_id = Id new_sym t

            s_eq_f = KV.structEqFunc kv

            nrpc_e = mkApp $ 
                           [ Var (Id s_eq_f TyUnknown)
                           , Type t
                           , eq_tc
                           , Var new_sym_id
                           , ce ]
        in
        Just (RuleReturnReplaceSymbFunc, 
            [s { expr_env = E.insertSymbolic new_sym_id eenv
               , curr_expr = CurrExpr Return (Var new_sym_id)
               , non_red_path_conds = non_red_path_conds s ++ [nrpc_e] }]
            , ng')
    | otherwise = 
      let
        t = typeOf ce
      in
      -- trace ("eq_tc = " ++ show (concreteSatStructEq kv tc t))
      Nothing

isApplyFrame :: Frame -> Bool
isApplyFrame (ApplyFrame _) = True
isApplyFrame _ = False


