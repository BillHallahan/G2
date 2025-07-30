{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes #-}

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

                          , isExecValueForm 
                          
                          , SymbolicFuncEval
                          , SymFuncTicks
                          , freshSymFuncTicks
                          , defSymFuncTicks
                          , retReplaceSymbFuncVar
                          , retReplaceSymbFuncTemplate
                          
                          , nonRedBlockerTick ) where

import G2.Config.Config
import G2.Execution.DataConPCMap
import G2.Execution.NewPC
import G2.Execution.NormalForms
import G2.Execution.PrimitiveEval
import G2.Execution.RuleTypes
import G2.Execution.SymToCase
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.Typing as T
import qualified G2.Language.KnownValues as KV
import G2.Language.Simplification
import qualified G2.Language.Stack as S
import G2.Preprocessing.NameCleaner
import G2.Solver hiding (Assert)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import qualified Data.List as L
import qualified Data.Sequence as S
import G2.Data.Utils
import qualified G2.Data.UFMap as UF
import qualified G2.Language.TyVarEnv as TV

import Control.Exception
import Control.Monad.Extra
import Data.Maybe
import Data.Traversable
import Data.Int (Int)
import Debug.Trace

stdReduce :: (Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> State t -> Bindings -> IO (Rule, [(State t, ())], Bindings)
stdReduce share symb_func_eval solver simplifier s b@(Bindings {name_gen = ng}) = do
    (r, s', ng') <- stdReduce' share symb_func_eval solver simplifier s ng
    let s'' = map (\ss -> ss { rules = r:rules ss }) s'
    return (r, zip s'' (repeat ()), b { name_gen = ng'})

stdReduce' :: (Solver solver, Simplifier simplifier) => Sharing -> SymbolicFuncEval t -> solver -> simplifier -> State t -> NameGen -> IO (Rule, [State t], NameGen)
stdReduce' share _ solver simplifier s@(State { curr_expr = CurrExpr Evaluate ce }) ng
    | Var i  <- ce
    , share == Sharing = return $ evalVarSharing s ng i
    | Var i <- ce
    , share == NoSharing = return $ evalVarNoSharing s ng i
    | App e1 e2 <- ce = do
        let (r, xs, ng') = evalApp s ng e1 e2
        (ng'', xs') <- mapAccumMaybeM (reduceNewPC solver simplifier) ng' xs
        return (r, xs', ng'')
    | Let b e <- ce = return $ evalLet s ng b e
    | Case e i t a <- ce = do
        let (r, xs, ng') = evalCase s ng e i t a
        (ng'', xs') <- mapAccumMaybeM (reduceNewPC solver simplifier) ng' xs
        return (r, xs', ng'')
    | Cast e c <- ce = return $ evalCast s ng e c
    | Tick t e <- ce = return $ evalTick s ng t e
    | NonDet es <- ce = return $ evalNonDet s ng es
    | SymGen sl t <- ce = return $ evalSymGen s ng sl t
    | Assume fc e1 e2 <- ce = return $ evalAssume s ng fc e1 e2
    | Assert fc e1 e2 <- ce = return $ evalAssert s ng fc e1 e2
    | otherwise = return (RuleReturn, [s { curr_expr = CurrExpr Return ce }], ng)
stdReduce' _ symb_func_eval solver simplifier s@(State { curr_expr = CurrExpr Return ce
                                 , exec_stack = stck }) ng
    | isError ce
    , Just (AssertFrame is _, stck') <- S.pop stck =
        return (RuleError, [s { exec_stack = stck'
                              , true_assert = True
                              , assert_ids = fmap (\fc -> fc { returns = Prim Error TyBottom }) is }], ng)
    | Just rs <- symb_func_eval defSymFuncTicks s ng ce = return rs
    | Just (UpdateFrame n, stck') <- frstck = return $ retUpdateFrame s ng n stck'
    | isError ce
    , Just (_, stck') <- S.pop stck = return (RuleError, [s { exec_stack = stck' }], ng)
    | Just (CaseFrame i t a, stck') <- frstck = return $ retCaseFrame s ng ce i t a stck'
    | Just (CastFrame c, stck') <- frstck = return $ retCastFrame s ng ce c stck'
    | Lam u i e <- ce
    , Just (ApplyFrame ae, stck') <- S.pop stck = return $ retLam s ng u i e ae stck'
    | Just (ApplyFrame e, stck') <- S.pop stck = return $ retApplyFrame s ng ce e stck'
    | Just (AssumeFrame e, stck') <- frstck = do
        let (r, xs, ng') = retAssumeFrame s ng ce e stck'
        (ng'', xs') <- mapAccumMaybeM (reduceNewPC solver simplifier) ng' xs
        return (r, xs', ng'')
    | Just (AssertFrame ais e, stck') <- frstck = do
        let (r, xs, ng') = retAssertFrame s ng ce ais e stck'
        (ng'', xs') <- mapAccumMaybeM (reduceNewPC solver simplifier) ng' xs
        return (r, xs', ng'')
    | Just (CurrExprFrame act e, stck') <- frstck = do
        let (r, xs, ng') = retCurrExpr s ce act e stck' ng
        (ng'', xs') <- mapAccumMaybeM (reduceNewPC solver simplifier) ng' xs
        return (r, xs', ng'')
    | Nothing <- frstck = return (RuleIdentity, [s], ng)
    | otherwise = error $ "stdReduce': Unknown Expr" ++ show ce ++ show (S.pop stck)
        where
            frstck = S.pop stck

            isError (Prim Error _) = True
            isError (Prim Undefined _) = True
            isError _ = False

mapAccumMaybeM :: Monad m => (s -> a -> m (Maybe (s, b))) -> s -> [a] -> m (s, [b])
mapAccumMaybeM f s xs = do
    (s', xs') <- mapAccumM f' s xs
    return (s', catMaybes xs')
    where
        f' s x = do
            r <- f s x
            case r of
                Just (s', x') -> return (s', Just x')
                Nothing -> return (s, Nothing)

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
evalApp :: State t -> NameGen -> Expr -> Expr -> (Rule, [NewPC t], NameGen)
evalApp s@(State { expr_env = eenv
                 , type_env = tenv
                 , known_values = kv
                 , exec_stack = stck
                 , tyvar_env = tvnv })
        ng e1 e2
    | ac@(Prim Error _) <- appCenter e1 =
        (RuleError, [newPCEmpty $ s { curr_expr = CurrExpr Return ac }], ng)
    -- Force evaluation of the expression being quantified over
    | (Prim ForAllPr _) <- e1 =
        let e2' = simplifyExprs eenv eenv e2 in
        (RuleEvalPrimToNorm, [newPCEmpty $ s { curr_expr = CurrExpr Return (App e1 e2') }], ng)
    -- Float ticks to the top of a prim
    | Prim _ _:es <- unApp (App e1 e2)
    , ts <- concatMap getTickish es
    , not (null ts) =
        let e = foldr Tick (stripAllTicks (App e1 e2)) ts in
       (RuleEvalPrimFloatTicks, [ (newPCEmpty $ s { curr_expr = CurrExpr Evaluate e })], ng)
    | Just (new_pc, ng') <- evalPrimWithState s ng (stripAllTicks $ App e1 e2) = (RuleEvalPrimToNormWithState, [new_pc], ng')
    | Just (e, eenv', pc, ng') <- evalPrimSymbolic tvnv eenv tenv ng kv (App e1 e2) =
        ( RuleEvalPrimToNormSymbolic
        , [ (newPCEmpty $ s { expr_env = eenv'
                            , curr_expr = CurrExpr Evaluate e }) { new_pcs = pc} ]
        , ng')
    | (Prim _ _):_ <- unApp (App e1 e2) = 
        let
            (exP, eenv') = evalPrimsSharing eenv tenv kv (App e1 e2)
        in
        ( RuleEvalPrimToNorm
        , [newPCEmpty $ s { expr_env = eenv', curr_expr = CurrExpr Return exP }]
        , ng)
    | isExprValueForm eenv (App e1 e2) =
        ( RuleReturnAppSWHNF
        , [newPCEmpty $ s { curr_expr = CurrExpr Return (App e1 e2) }]
        , ng)
    | otherwise =
        let
            frame = ApplyFrame e2
            stck' = S.push frame stck
        in
        ( RuleEvalApp e2
        , [newPCEmpty $ s { curr_expr = CurrExpr Evaluate e1
                          , exec_stack = stck' }]
        , ng)
    where
        getTickish (Tick t e) = t:getTickish e
        getTickish _ = []

evalLam :: State t -> LamUse -> Id -> Expr -> (Rule, [State t])
evalLam = undefined

retLam :: State t -> NameGen -> LamUse -> Id -> Expr -> Expr -> S.Stack Frame -> (Rule, [State t], NameGen)
retLam s@(State { expr_env = eenv, tyvar_env = tvnv })
       ng u i e ae stck'
    | TypeL <- u =
        case TV.deepLookup tvnv ae of
        Just t ->
            let 
                (n', ng') = freshSeededName (idName i) ng 
                e' = rename (idName i) n' e
                tvnv' = TV.insert n' t tvnv
                -- (eenv', e'', ng'', news) = liftBind i (Type t) eenv e' ng'

            in 
           ( RuleReturnEApplyLamType [n']
            , [ s { expr_env = eenv
                 , curr_expr = CurrExpr Evaluate e'
                 , exec_stack = stck' 
                 , tyvar_env = tvnv' } ]
            , ng' )
        Nothing -> error $ "retLam: Bad type\ni = " ++ show i
    | otherwise =
        let
            (eenv', e', ng', news) = liftBind i ae eenv e ng
        in
        ( RuleReturnEApplyLamExpr [news]
        , [s { expr_env = eenv'
             , curr_expr = CurrExpr Evaluate e'
             , exec_stack = stck' }]
        , ng' )

traceType :: E.ExprEnv -> Expr -> Maybe Type
traceType _ (Type t) = Just t
-- return symoblic type varaible if the varabile we lookup is symoblic in the expression env
traceType eenv (Var (Id n _)) = case E.lookupConcOrSym n eenv of 
                                        Just (E.Sym i) -> Just (TyVar i)
                                        Just (E.Conc e) -> traceType eenv e
                                        Nothing -> Nothing
traceType _ _ = Nothing

evalLet :: State t -> NameGen -> Binds -> Expr -> (Rule, [State t], NameGen)
evalLet s@(State { expr_env = eenv }) 
        ng binds e =
    let
        (binds_lhs, binds_rhs) = unzip binds

        olds = map idName binds_lhs
        (news, ng') = freshSeededNames olds ng

        e' = renameExprs (zip olds news) e
        binds_rhs' = renameExprs (zip olds news) binds_rhs

        eenv' = E.insertExprs (zip news binds_rhs') eenv
    in
    (RuleEvalLet news, [s { expr_env = eenv'
                          , curr_expr = CurrExpr Evaluate e'}]
                     , ng')

-- | Handle the Case forms of Evaluate.
evalCase :: State t -> NameGen -> Expr -> Id -> Type -> [Alt] -> (Rule, [NewPC t], NameGen)
evalCase s@(State { expr_env = eenv
                  , exec_stack = stck
                  , known_values = kv
                  , tyvar_env = tvnv })
         ng mexpr bind t alts
  -- Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | (Lit lit) <- unsafeElimOuterCast mexpr
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
      let 
          binds = [(bind, Lit lit)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseLit
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng)

  -- Is the current expression able to match a data consturctor based `Alt`?
  -- If so, then we bind all the parameters to the appropriate arguments and
  -- proceed with the evaluation of the `Alt`'s expression. We also make sure
  -- to perform the cvar binding.
  -- We unwrap the outermost cast from the mexpr.  It must be being cast
  -- to the DataCon type, so this is safe, and needed for our pattern matching.
  -- We do not want to remove casting from any of the arguments since this could
  -- mess up there types later
  | (Data dcon):ar <- unApp $ exprInCasts mexpr
  , ar' <- drop (length (dc_univ_tyvars dcon)) ar 
  , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts =
      let
          dbind = [(bind, mexpr)]
          expr' = liftCaseBinds dbind expr
          pbinds = zip params ar'
          (eenv', expr'', ng', news) = liftBinds tvnv kv pbinds eenv expr' ng
         
      in 
         assert (length params == length ar')
         ( RuleEvalCaseData news
         , [newPCEmpty $ s { expr_env = eenv'
                           , curr_expr = CurrExpr Evaluate expr''}] 
         , ng')

  -- We are not able to match any constructor but don't have a symbolic variable?
  -- We hit a DEFAULT instead.
  -- We perform the cvar binding and proceed with the alt
  -- expression.
  | e:_ <- unApp $ unsafeElimOuterCast mexpr
  , isData e
      || isLit e
      || isLam e
      || (case e of Var i@(Id n _) -> E.isSymbolic n eenv && hasFuncType (typeOf tvnv i); _ -> False)
  , (Alt _ expr):_ <- matchDefaultAlts alts =
      let 
          binds = [(bind, mexpr)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseDefault
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }], ng)

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

        alt_res = dsts_cs ++ lsts_cs ++ def_sts
      in
      -- We return exactly one state per branch, unless we are concretizing a MutVar.
      -- In that case, we will return at least one state, but might return an unbounded
      -- number more- see Note [MutVar Copy Concretization].
      assert (tyConName (tyAppCenter $ typeOf tvnv mexpr) == Just (KV.tyMutVar kv)
                        ==> length alt_res >= length dalts + length lalts + length defs)
      assert (tyConName (tyAppCenter $ typeOf tvnv mexpr) /= Just (KV.tyMutVar kv)
                        ==> length alt_res == length dalts + length lalts + length defs)
      (RuleEvalCaseSym, alt_res, ng'')

  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
  -- is only done when the matching expression is NOT in value form. Value
  -- forms should be handled by other RuleEvalCase* rules.
  | not (isExprValueForm eenv mexpr) =
      let frame = CaseFrame bind t alts
      in ( RuleEvalCaseNonVal
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate mexpr
                           , exec_stack = S.push frame stck }], ng)

  -- If the list of alts is empty, that normally means that the bindee is guaranteed
  -- to be bottom (either evaluate to an error or not terminate.)  In either case, we would normally
  -- never then actually try to branch on the case.  However, the executor might reach
  -- this put if NRPCs are being used, as a bottoming expression may be replaced by a
  -- symbolic variable.
  | [] <- alts = (RuleEvalCaseBottom, [newPCEmpty $ s { curr_expr = CurrExpr Evaluate (Prim Error TyBottom) }], ng)

  | otherwise = error $ "reduceCase: bad case passed in\n" ++ show mexpr ++ "\n" ++ show alts
  where
        tyConName (TyCon n _) = Just n
        tyConName _ = Nothing

-- | DEFAULT `Alt`s.
matchDefaultAlts :: [Alt] -> [Alt]
matchDefaultAlts alts = [a | a@(Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts (DataCon n _ _ _) alts =
  [a | a@(Alt (DataAlt (DataCon n' _ _ _) _) _) <- alts, n == n']

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a@(Alt (LitAlt alit) _) <- alts, lit == alit]

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
defaultAlts alts = [a | a@(Alt Default _) <- alts]

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
concretizeVarExpr' s@(State {expr_env = eenv, type_env = tenv, known_values = kv, tyvar_env = tvnv})
                ngen mexpr_id cvar (dcon, params, aexpr) maybeC =
          (NewPC { state =  s { expr_env = eenv''
                              , curr_expr = CurrExpr Evaluate aexpr''}
                 -- It is VERY important that we insert the mexpr_id in `concretized`
                 -- This forces reduceNewPC to check that the concretized data constructor does
                 -- not violate any path constraints from default cases. 
                 , new_pcs = pcs
                 , concretized = [mexpr_id]
                 }, ngen'')
  where
    mexpr_t = typeOf tvnv mexpr_id
    (news, dcon', ngen', aexpr') = cleanParamsAndMakeDcon tvnv params ngen dcon aexpr mexpr_t tenv

    -- Apply cast, in opposite direction of unsafeElimOuterCast
    dcon'' = case maybeC of 
                (Just (t1 :~ t2)) -> Cast dcon' (t2 :~ t1)
                Nothing -> dcon'

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, (Var mexpr_id))]
    aexpr'' = liftCaseBinds binds aexpr'

    (eenv'', pcs, ngen'') = adjustExprEnvAndPathConds tvnv kv tenv eenv ngen' dcon dcon'' mexpr_id params news

cleanParamsAndMakeDcon :: TV.TyVarEnv -> [Id] -> NameGen -> DataCon -> Expr -> Type -> TypeEnv -> ([Name], Expr, NameGen, Expr)
cleanParamsAndMakeDcon tv params ngen dcon aexpr mexpr_t tenv =
    let
        -- Make sure that the parameters do not conflict in their symbolic reps.
        olds = map idName params
        clean_olds = map cleanName olds

        (news, ngen') = freshSeededNames clean_olds ngen

        (dcon', aexpr') = renameExprs (zip olds news) (Data dcon, aexpr)

        newparams = map (uncurry Id) $ zip news (map (typeOf tv) params)
        dConArgs = (map (Var) newparams)

        -- Get list of Types to concretize polymorphic data constructor and concatenate with other arguments
        type_ars = mexprTyToExpr mexpr_t tenv
        exprs = [dcon'] ++ type_ars ++ dConArgs

        -- Apply list of types (if present) and DataCon children to DataCon
        dcon'' = mkApp exprs
    in
    (news, dcon'', ngen', aexpr')

-- [String Concretizations and Constraints]
-- Generally speaking, the values of symbolic variable are determined by one of two methods:
-- in the case of primitive values (Int#, Float#, ...), we generate path constraints, which can be solved
-- via an SMT solver.  In the case of algebraic data types, we use concretization, in which
-- the symbolic variable is replaced by a (partially) concrete expression.
--
-- We play a bit of a funny trick for Strings.  In Haskell, String is really just a type alias
-- for a list of Chars:
--     type String = [Char]  
-- The obvious thing to do, then, is just allow concretization to kick in: and indeed, this is sometimes
-- necessary, if a String is directly pattern matched on, or if a String is passed to a function expecting
-- a generic list [a].
--
-- However, SMT solvers also support reasoning about Strings, and concretization can sometimes lead to a blow up
-- in the state space. For instance, when applying
--     show :: Int -> String
-- concretization would result in infinite recursive branching to potentially print different Ints. 
-- Thus, it is appealing to allow reasoning about Strings in the SMT solver, when possible, to avoid this blowup. 
--
-- In principle, allowing reasoning about Strings both via concretization and the SMT solver: we simply perform both
-- concretization and path constraint generation.  Care must be taken to keep this in sync.  That is, we must
-- ensure that the value of a String is equally constrained by both the concretization and the generated path constraints.
-- When a String s is concretized to the empty String, [], we generate a path constraint that `strLen s == 0`.
-- When a String s is concretized to a cons, (C# c:xs), we generate a path constraint that `c ++ xs == s`.
-- Note that in the cons case, we must also concretize the Char in the list to obtain the primitive Char#,
-- as this will be the symbolic variable that may be inserted into other path constraints.

-- | Determines an ExprEnv and Path Constraints from following a particular branch of symbolic execution.
-- Has special handling for Strings- see [String Concretizations and Constraints]
adjustExprEnvAndPathConds :: TV.TyVarEnv 
                  -> KnownValues
                  -> TypeEnv
                  -> ExprEnv
                  -> NameGen
                  -> DataCon -- ^ The data con in the scrutinee (as in `case scrutinee of ...`)
                  -> Expr -- ^ The scrutinee
                  -> Id -- ^ Symbolic Variable Id 
                  -> [Id] -- ^ Constructor Argument Ids
                  -> [Name]
                  -> (ExprEnv, [PathCond], NameGen)
adjustExprEnvAndPathConds tv kv tenv eenv ng dc dc_e mexpr params dc_args
    | Just dcpcs <- HM.lookup (dcName dc) (dcpcMap tv kv tenv)
    , _:ty_args <- unTyApp $ typeOf tv mexpr
    , Just dcpc <- L.lookup ty_args dcpcs = 
        let 
            (eenv''', pcs, ng', _) = applyDCPC ng eenv'' new_ids (Var mexpr) dcpc
        in
        (eenv''', pcs, ng')
    | otherwise = (eenv'', [], ng)
    where
        mexpr_n = idName mexpr
        -- Update the expr environment
        new_ids = zipWith (\(Id _ t) n -> Id n t) params dc_args
        eenv' = foldr E.insertSymbolic eenv new_ids
        -- Concretizes the mexpr to have same form as the DataCon specified
        eenv'' = E.insert mexpr_n dc_e eenv' 

-- | Given the Type of the matched Expr, looks for Type in the TypeEnv, and returns Expr level representation of the Type
mexprTyToExpr :: Type -> TypeEnv -> [Expr]
mexprTyToExpr mexpr_t = reverse . mexprTyToExpr' mexpr_t

mexprTyToExpr' :: Type -> TypeEnv -> [Expr]
mexprTyToExpr' mexpr_t tenv 
    -- special case for NewTyCon, involves looking up tyVars and binding them to concrete types specified by mexpr_t
    | Just (algDataTy, bindings) <- getAlgDataTy mexpr_t tenv     
    , NewTyCon {} <- algDataTy = dconTyToExpr (data_con algDataTy) bindings
    | otherwise = typeToExpr mexpr_t

-- | Given a DataCon, and an (Id, Type) mapping, returns list of Expression level Type Arguments to DataCon
dconTyToExpr :: DataCon -> [(Id, Type)] -> [Expr]
dconTyToExpr (DataCon _ t _ _) bindings =
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

-- | Creating a path constraint.  The passed Expr should have type Bool or type [Char].
-- In the latter case, the note [String Concretizations and Constraints] is relevant.
createExtCond :: State t -> NameGen -> Expr -> Id -> (DataCon, [Id], Expr) -> (NewPC t, NameGen)
createExtCond s ngen mexpr cvar (dcon, bindees, aexpr)
    | typeOf tvnv mexpr == tyBool kv =
        let
            -- Get the Bool value specified by the matching DataCon
            -- Throws an error if dcon is not a Bool Data Constructor
            boolValue = getBoolFromDataCon (known_values s) dcon
            cond = ExtCond mexpr boolValue

            -- Now do a round of rename for binding the cvar.
            binds = [(cvar, mexpr)]
            aexpr' = liftCaseBinds binds aexpr
            res = s {curr_expr = CurrExpr Evaluate aexpr'}
        in
        (NewPC { state = res, new_pcs = [cond] , concretized = []}, ngen)
    | Just dcpcs <- HM.lookup (dcName dcon) (dcpcMap tvnv kv tenv)
    , _:ty_args <- unTyApp $ typeOf tvnv mexpr
    , Just dcpc <- L.lookup ty_args dcpcs = 
        let
            mexpr_t = typeOf tvnv mexpr
            (news, dcon', ngen', aexpr') = cleanParamsAndMakeDcon tvnv bindees ngen dcon aexpr mexpr_t tenv

            new_ids = zipWith (\(Id _ t) n -> Id n t) bindees news
            eenv = foldr E.insertSymbolic (expr_env s) new_ids

            (eenv', pcs, ngen'', bindee_exprs) = applyDCPC ngen' eenv new_ids mexpr dcpc

            -- Bind the cvar and bindees
            binds = (cvar, dcon'):zip new_ids bindee_exprs
            aexpr'' = liftCaseBinds binds aexpr'

            res = s { expr_env = eenv', curr_expr = CurrExpr Evaluate aexpr'' }
        in
        (NewPC { state = res, new_pcs = pcs, concretized = [] }, ngen'')
        -- the issue is located below for concRead 
    | otherwise = error $ "createExtCond: unsupported type" ++ "\n" ++ show (typeOf tvnv mexpr) ++ "\n" ++ show dcon
        where
            kv = known_values s
            tenv = type_env s
            tvnv = tyvar_env s

getBoolFromDataCon :: KnownValues -> DataCon -> Bool
getBoolFromDataCon kv dcon
    | (DataCon dconName dconType [] []) <- dcon
    , dconType == (tyBool kv)
    , dconName == (KV.dcTrue kv) = True
    | (DataCon dconName dconType [] []) <- dcon
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
        Just aexpr -> liftSymDefAlt' s ng mexpr aexpr cvar as -- (liftSymDefAlt'' s mexpr aexpr cvar as, ng)
        _ -> ([], ng)

-- Note [MutVar Copy Concretization]
-- We must consider two possibilities when concretizing a MutVar:
--
--   1) The MutVar is a new MutVar, containing a fresh symbolic value
--
--   2) The MutVar is the same as some other MutVar that was previously concretized from a symbolic
--      variable, and thus refers to the same mutable value.
--
-- To see why each of these possibilities must be considered, refer to the below program:
--
-- @
-- k :: MutVar# RealWorld Int -> MutVar# RealWorld Int -> (Int, Int)
-- k mv1 mv2 =
--     let
--         s1 = writeMutVar# mv1 2 realWorld#
--         s2 = writeMutVar# mv2 6 s1
 
--         (# s3, x1 #) = readMutVar# mv1 s2
--         (# s4, x2 #) = readMutVar# mv2 s3 
--     in
--     (x1, x2)
-- @
--
-- If mv1 and mv2 are different mutable variables, the functuon `k` will return the tuple (2, 6).
-- However, if mv1 and mv2 are the same mutable variable, then `k` will return the tuple (6, 6).
--
-- Note that possibility (2) only involves concretizing MutVars to other MutVars that were themselves
-- concretized from symbolic variables, not MutVars introduced by newMutVar#.  This is due to ordering:
-- if we have a symbolic MutVar mv1, and then introduce a new MutVar mv2 via newMutVar#, clearly
-- mv1 and mv2 must be distinct.  We use `MVOrigin`, in G2.Language.MutVar, to track whether a MutVar
-- came from concretization or newMutVar#. 

-- | Concretize Symbolic variable to Case Expr on its possible Data Constructors
liftSymDefAlt' :: State t -> NameGen -> Expr -> Expr -> Id -> [Alt] -> ([NewPC t], NameGen)
liftSymDefAlt' s@(State { type_env = tenv, known_values = kv, tyvar_env = tvnv }) ng mexpr aexpr cvar alts
    | Var i:_ <- unApp mexpr
    , TyApp (TyApp mvt realworld_ty) stored_ty <- typeOf tvnv i
    , TyCon n _ <- tyAppCenter mvt
    , n == KV.tyMutVar (known_values s) =
        let
            binds = [(cvar, getExpr nmv_s)]
            aexpr' = liftCaseBinds binds aexpr

            -- Create a new mutable variable with a symbolic stored value
            (stored_var, ng') = freshSeededId (idName i) stored_ty ng
            (nmv_s, ng'') = newMutVar s ng' MVSymbolic realworld_ty stored_ty (Var stored_var)
            
            eenv' = E.insertSymbolic stored_var $ E.insert (idName i) (getExpr nmv_s) (expr_env nmv_s)
            nmv_s' = nmv_s { curr_expr = CurrExpr Evaluate aexpr', expr_env = eenv' }

            -- Consider that the new mutable variable might be some existing mutable variable.
            -- See Note [MutVar Copy Concretization].
            mv_ty = mutVarTy (known_values s) realworld_ty stored_ty
            rel_mutvar = HM.keys
                       $ HM.filter (\MVInfo { mv_val_id = Id _ t
                                            , mv_origin = org } -> t == stored_ty && org == MVSymbolic) (mutvar_env s)
            copy_states = map (\mv -> s { curr_expr = CurrExpr Evaluate aexpr'
                                        , expr_env = E.insert (idName i) (Prim (MutVar mv) mv_ty) (expr_env s)
                                        }
                              ) rel_mutvar
        in
        (map newPCEmpty (nmv_s':copy_states), ng'')
    | (Var i):_ <- unApp $ exprInCasts mexpr = -- Id with original Type
        let cty = case mexpr of
                Cast _ (_ :~ t2) -> t2
                _ -> typeOf tvnv mexpr

            (adt, bi) = case getCastedAlgDataTy cty tenv of 
                            Just adt_bi -> adt_bi
                            Nothing -> error $ "we are failling on " ++ show cty
            maybeC = case mexpr of
                (Cast _ c) -> Just c
                _ -> Nothing
            dcs = dataCon adt

            -- Find DCs already accounted for by other case alts
            badDCs = mapMaybe (\alt -> case alt of
                (Alt (DataAlt (DataCon dcn _ _ _) _) _) -> Just dcn
                _ -> Nothing) alts
        in
        case null badDCs of
            True ->
                let
                    (cvar', ng') = freshSeededId cvar (typeOf tvnv cvar) ng

                    binds = [(cvar, Var cvar')]
                    aexpr' = liftCaseBinds binds aexpr

                    s' = s { curr_expr = CurrExpr Evaluate aexpr'
                           , expr_env = E.insert (idName cvar') mexpr (expr_env s)}
                in
                ([NewPC { state = s', new_pcs = [], concretized = [] }], ng')
            False ->
                let
                    -- Find DCs NOT accounted for by other case alts, i.e. that would go
                    -- down the default path
                    dcs' = filter (\(DataCon dcn _ _ _) -> dcn `notElem` badDCs) dcs

                    (cvar', ng') = freshSeededId cvar (typeOf tvnv cvar) ng

                    -- -- Create a case expression to choose on of viable DCs
                    (_, mexpr', assume_pc, eenv', ng'') = createCaseExpr tvnv bi maybeC cvar' (typeOf tvnv i) kv tenv (expr_env s) ng' dcs'

                    binds = [(cvar, Var cvar')]
                    aexpr' = liftCaseBinds binds aexpr

                    eenv'' = E.insert (idName cvar') mexpr'
                           $ E.insert (idName i) mexpr' eenv'
                    s' = s { curr_expr = CurrExpr Evaluate aexpr'
                           , expr_env = eenv'' }
                in
                ([NewPC { state = s', new_pcs = assume_pc, concretized = [] }], ng'')
    | Prim _ _:_ <- unApp mexpr = (liftSymDefAlt'' s mexpr aexpr cvar alts, ng)
    | isPrimType (typeOf tvnv mexpr) = (liftSymDefAlt'' s mexpr aexpr cvar alts, ng)
    | TyVar _ <- (typeOf tvnv mexpr) = 
                let
                    (cvar', ng') = freshId (typeOf tvnv cvar) ng 
                    eenv' =  E.insert (idName cvar') mexpr (expr_env s)
                    aexpr' = replaceVar (idName cvar) (Var cvar') aexpr
                    s' = s {curr_expr = CurrExpr Evaluate aexpr', expr_env = eenv'}

                in ([NewPC {state = s', new_pcs = [], concretized = []}], ng')
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

defAltExpr :: [Alt] -> Maybe Expr
defAltExpr [] = Nothing
defAltExpr (Alt Default e:_) = Just e
defAltExpr (_:xs) = defAltExpr xs

----------------------------------------------------

evalCast :: State t -> NameGen -> Expr -> Coercion -> (Rule, [State t], NameGen)
evalCast s@(State { expr_env = eenv
                  , exec_stack = stck 
                  , tyvar_env = tvnv }) 
         ng e c@(t1 :~ t2)
    | Var (Id n _) <- e
    , E.isSymbolic n eenv
    , hasFuncType t2 && not (hasFuncType t1) =
        let
            (i, ng') = freshId t2 ng
            new_e = Cast (Var i) (t2 :~ t1)
        in
        ( RuleOther
        , [s { expr_env = E.insertSymbolic i $ E.insert n new_e eenv
             , curr_expr = CurrExpr Return (Var i) }]
        , ng')
    | cast <- Cast e c
    , (cast', ng') <- splitCast tvnv ng cast
    , cast /= cast' =
        ( RuleEvalCastSplit
        , [ s { curr_expr = CurrExpr Evaluate $ simplifyCasts cast' }]
        , ng')
    | otherwise =
        ( RuleEvalCast
        , [s { curr_expr = CurrExpr Evaluate $ simplifyCasts e
             , exec_stack = S.push frame stck}]
        , ng)
    where
        
        frame = CastFrame c

evalTick :: State t -> NameGen -> Tickish -> Expr -> (Rule, [State t], NameGen)
evalTick s ng (HpcTick i tm) e =
    (RuleTick, [ s { curr_expr = CurrExpr Evaluate e, reached_hpc = HS.insert (i, tm) (reached_hpc s) }], ng)
evalTick s ng _ e = (RuleTick, [ s { curr_expr = CurrExpr Evaluate e }], ng)

evalNonDet :: State t -> NameGen -> [Expr] -> (Rule, [State t], NameGen)
evalNonDet s ng es =
    let
        s' = map (\e -> s { curr_expr = CurrExpr Evaluate e }) es
    in
    (RuleNonDet, s', ng)

evalSymGen :: State t -> NameGen -> SymLog -> Type -> (Rule, [State t], NameGen)
evalSymGen s@( State { expr_env = eenv }) 
           ng sl t =
    let
          (n, ng') = freshSeededString "symG" ng
          i = Id n t

          eenv' = E.insertSymbolic i eenv
          sg = case sl of
                    SLog -> sym_gens s S.:|> n
                    SNoLog -> sym_gens s
    in
    (RuleSymGen, [s { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate (Var i)
                    , sym_gens = sg }]
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
    | Var _ <- e =
       ( RuleReturnEUpdateVar un
       , [s { expr_env = E.insert un e eenv
            , curr_expr = CurrExpr Return e
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

retCaseFrame :: State t -> NameGen -> Expr -> Id -> Type -> [Alt] -> S.Stack Frame -> (Rule, [State t], NameGen)
retCaseFrame s b e i t a stck =
    ( RuleReturnECase
    , [s { curr_expr = CurrExpr Evaluate (Case e i t a)
         , exec_stack = stck }]
    , b)

retCastFrame :: State t -> NameGen -> Expr -> Coercion -> S.Stack Frame -> (Rule, [State t], NameGen)
retCastFrame s ng e c stck =
    ( RuleReturnCast
    , [s { curr_expr = CurrExpr Return $ simplifyCasts $ Cast e c
         , exec_stack = stck}]
    , ng)

retCurrExpr :: State t -> Expr -> CEAction -> CurrExpr -> S.Stack Frame -> NameGen -> (Rule, [NewPC t], NameGen)
retCurrExpr s@(State { expr_env = eenv, known_values = kv, tyvar_env = tvnv }) e1 (EnsureEq e2) orig_ce@(CurrExpr _ ce) stck ng
    | Just (eenv', new_pc, new_nrpc_pairs) <- matchPairs tvnv kv e1 e2 (eenv, [], []) =
        let
            (ng', nrpc) = foldr (\(p_e1, p_e2) (ng_, nrpcs) ->
                                let
                                    (p_e1', ng_') = addNRPCTick ng_ p_e1
                                    (p_e2', ng_'') = addNRPCTick ng_' p_e2
                                in
                                (ng_'', (p_e1', p_e2') S.:<| nrpcs))
                            (ng, non_red_path_conds s)
                            new_nrpc_pairs
        in
        ( RuleReturnCurrExprFr
        , [NewPC { state = s { expr_env = eenv'
                             , curr_expr = CurrExpr Evaluate ce
                             , exec_stack = stck
                             , non_red_path_conds = nrpc }
                    , new_pcs = new_pc
                    , concretized = [] }], ng' )
    | otherwise =
        assert (not (isExprValueForm eenv e2))
                ( RuleReturnCurrExprFr
                , [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                                    , non_red_path_conds = non_red_path_conds s
                                    , exec_stack = S.push (CurrExprFrame (EnsureEq e1) orig_ce) stck}
                        , new_pcs = []
                        , concretized = [] }], ng )

retCurrExpr s _ NoAction orig_ce stck ng = 
    ( RuleReturnCurrExprFr
    , [NewPC { state = s { curr_expr = orig_ce
                         , exec_stack = stck}
             , new_pcs = []
             , concretized = []}], ng )

matchPairs :: TV.TyVarEnv -> KnownValues -> Expr -> Expr -> (ExprEnv, [PathCond], [(Expr, Expr)]) -> Maybe (ExprEnv, [PathCond], [(Expr, Expr)])
matchPairs tvnv kv e1 e2 eenv_pc_ee@(eenv, pc, ees)
    | Var (Id n _) <- e1
    , Just (E.Conc e1') <- E.lookupConcOrSym n eenv = matchPairs tvnv kv e1' e2 eenv_pc_ee
    | Var (Id n _) <- e2
    , Just (E.Conc e2') <- E.lookupConcOrSym n eenv = matchPairs tvnv kv e1 e2' eenv_pc_ee
    | e1 == e2 = Just eenv_pc_ee
    | Cast e1' c1 <- e1
    , Cast e2' c2 <- e2
    , c1 == c2 =  matchPairs tvnv kv e1' e2' eenv_pc_ee

    | isExprValueForm eenv e1
    , isExprValueForm eenv e2
    , t1 <- typeOf tvnv e1
    -- We can always add to the path constraints if we have a type that is primitive or Bool.
    , isPrimType t1 || t1 == tyBool kv
    -- We can also add to the path constraints if we have a primitive expression
    -- that returns a list
    || isPrimApp e1 || isPrimApp e2 =
        assert (typeOf tvnv e2 == t1)
        Just (eenv, ExtCond (inline eenv HS.empty $ mkEqPrimExpr tvnv kv e1 e2) True:pc, ees)

    -- Symmetric cases for e1/e2 being  symbolic variables 
    | Var (Id n t) <- e1
    , E.isSymbolic n eenv
    , not (isPrimType t || t == tyBool kv) =
        Just (E.insert n e2 eenv, pc, ees)
    | Var (Id n t) <- e2
    , E.isSymbolic n eenv
    , not (isPrimType t || t == tyBool kv) =
        Just (E.insert n e1 eenv, pc, ees)

    | Data dc1:es1 <- unApp e1
    , Data dc2:es2 <- unApp e2 =
        let addPair p (eenv', pc', ees') = (eenv', pc', p:ees') in
        case dcName dc1 == dcName dc2 of
            True -> Just $ foldr (\es1es2@(es1_, es2_) epe -> fromMaybe (addPair es1es2 epe) (matchPairs tvnv kv es1_ es2_ epe)) eenv_pc_ee $ zip es1 es2
            False ->
                Just (eenv, [ExtCond (mkFalse kv) True], [])
    | otherwise = Nothing
    where
        isPrimApp (App e _) = isPrimApp e
        isPrimApp (Prim _ _) = True
        isPrimApp _ = False

        inline :: ExprEnv -> HS.HashSet Name -> Expr -> Expr
        inline h ns v@(Var (Id n _))
            | E.isSymbolic n h = v
            | HS.member n ns = v
            | Just e <- E.lookup n h
            , not (isLam e) = inline h (HS.insert n ns) e
        inline h ns e = modifyChildren (inline h ns) e

addNRPCTick :: NameGen -> Expr -> (Expr, NameGen)
addNRPCTick ng e | c@(Var _):es <- unApp e =
    let (c', ng') = nonRedBlockerTick ng c in (mkApp $ c':es, ng')
addNRPCTick ng e = (e, ng)

nonRedBlockerTick :: NameGen -> Expr -> (Expr, NameGen)
nonRedBlockerTick ng e =
    let (n, ng') = freshSeededName (Name "NonRedBlocker" Nothing 0 Nothing) ng in
    (Tick (NamedLoc n) e, ng')

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
            [Data (DataCon dcn _ _ _)]
                | dcn == KV.dcFalse kv -> ([], ng)
                | dcn == KV.dcTrue kv ->
                    ( [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                                         , exec_stack = stck }
                             , new_pcs = []
                             , concretized = [] }]
                    , ng)
            (Var i@(Id _ _)):_ -> concretizeExprToBool s ng i dalt e2 stck
            _ -> addExtCond s ng e1 e2 stck
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
            [Data (DataCon dcn _ _ _)]
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
            _ -> addExtConds s ng e1 ais e2 stck
            
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
                ngen mexpr_id dcon@(DataCon dconName _ _ _) e2 stck = 
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

addExtCond :: State t -> NameGen -> Expr -> Expr -> S.Stack Frame -> ([NewPC t], NameGen)
addExtCond s ng e1 e2 stck = 
    ([NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 True]
             , concretized = [] }], ng)

addExtConds :: State t -> NameGen -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> ([NewPC t], NameGen)
addExtConds s ng e1 ais e2 stck =
    let
        s' = s { curr_expr = CurrExpr Evaluate e2
               , exec_stack = stck}

        condt = [ExtCond e1 True]
        condf = [ExtCond e1 False]

        strue = NewPC { state = s'
                      , new_pcs = condt
                      , concretized = []}

        sfalse = NewPC { state = s' { true_assert = True
                                    , assert_ids = ais }
                       , new_pcs = condf
                       , concretized = []}
    in
    ([strue, sfalse], ng)

-- This function aims to extract pairs of types being coerced between. Given a coercion t1 :~ t2, the tuple (t1, t2) is returned.
extractTypes :: KnownValues -> Id -> (Type, Type)
extractTypes kv (Id _ (TyApp (TyApp (TyApp (TyApp (TyCon n _) _) _) n1) n2)) =
        (if KV.tyCoercion kv == n 
        then    
           (n1, n2)
        else
            error "ExtractTypes: the center of the pattern is not a coercion")
extractTypes _ _ = error "ExtractTypes: The type of the pattern doesn't have four nested TyApp while its corresponding scrutinee is a coercion"

liftBinds :: TV.TyVarEnv -> KnownValues -> [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, [Name])
liftBinds tv kv binds eenv expr ngen = (eenv', expr'', ngen', news)

  where
    -- Converts type variables into corresponding types as determined by coercions
    -- For example, in 'E a b c' where 
    -- 'a ~# Int', 'b ~# Float', 'c ~# String'
    -- The code simply does the following:  
    -- 'E a b c' -> 'E Int Float String'
    (coercion, value_args) = L.partition (\(_, e) -> case e of
                                        Coercion _ -> True
                                        _ -> False) binds
    
    extract_tys = map (extractTypes kv . fst) coercion

    uf_map = foldM (\uf_map' (t1, t2) -> T.unify' uf_map' t1 t2) UF.empty extract_tys
    
    expr' = case uf_map of
            Nothing -> expr
            Just uf_map' -> L.foldl' (\e (n,t) -> retype (Id n (typeOf tv t)) t e) expr (HM.toList $ UF.toSimpleMap uf_map')
    
    -- bindsLHS is the pattern
    -- bindsRHS is the scrutinee 
    (bindsLHS, bindsRHS) = unzip value_args
    
    olds = map idName bindsLHS
    (news, ngen') = freshSeededNames olds ngen

    olds_news = HM.fromList $ zip olds news

    eenv' = E.insertExprs (zip news bindsRHS) eenv

    expr'' = renamesExprs olds_news expr'

liftBind :: Id -> Expr -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, Name)
liftBind bindsLHS bindsRHS eenv expr ngen = (eenv', expr', ngen', new)
  where
    old = idName bindsLHS
    (new, ngen') = freshSeededName old ngen

    expr' = renameExpr old new expr

    eenv' = E.insert new bindsRHS eenv

type SymbolicFuncEval t = SymFuncTicks -> State t -> NameGen -> Expr -> Maybe (Rule, [State t], NameGen)

hpcTick :: Int -> Tickish
hpcTick u = HpcTick u "HPC"

freshHpcTick :: NameGen -> (Tickish, NameGen)
freshHpcTick ng =
    let (Name n _ u _, ng') = freshSeededName (Name "HPC" Nothing 0 Nothing) ng in
    (HpcTick u "HPC", ng')

data SymFuncTicks = SFT { dc_split_tick :: Tickish
                        , func_split_tick :: Tickish
                        , lit_split_tick :: Tickish
                        , const_tick :: Tickish }

defSymFuncTicks :: SymFuncTicks
defSymFuncTicks = SFT { dc_split_tick = hpcTick 1 
                      , func_split_tick = hpcTick 2
                      , lit_split_tick = hpcTick 3
                      , const_tick = hpcTick 4 }

freshSymFuncTicks :: NameGen -> (SymFuncTicks, NameGen)
freshSymFuncTicks ng =
    let
        (ds, ng2) = freshHpcTick ng
        (fs, ng3) = freshHpcTick ng2
        (ls, ng4) = freshHpcTick ng3
        (cs, ng5) = freshHpcTick ng4

        sft = SFT { dc_split_tick = ds
                  , func_split_tick = fs
                  , lit_split_tick = ls
                  , const_tick = cs}
    in
    (sft, ng5)

-- change literal rule to only match on arguments
retReplaceSymbFuncTemplate :: SymFuncTicks -> State t -> NameGen -> Expr -> Maybe (Rule, [State t], NameGen)
retReplaceSymbFuncTemplate sft
                           s@(State { expr_env = eenv
                                    , type_env = tenv
                                    , known_values = kv })
                           ng ce

    -- DC-SPLIT
    | Var (Id n (TyFun t1 t2)):es <- unApp ce
    , TyCon tname _:ts <- unTyApp t1 
    , E.isSymbolic n eenv
    , Just alg_data_ty <- HM.lookup tname tenv
    = let
        ty_map = HM.fromList $ zip (map idName bound) ts

        dcs = applyTypeHashMap ty_map $ dataCon alg_data_ty
        bound = applyTypeHashMap ty_map $ bound_ids alg_data_ty

        (x, ng') = freshId t1 ng
        (x', ng'') = freshId t1 ng'
        (alts, symIds, ng''') =
            -- TODO: Is it true we can ignore the universial and existential type variable in dc split?
            foldr (\dc@(DataCon _ dcty _ _) (as, sids, ng1) ->
                        let (argIds, ng1') = genArgIds dc ng1
                            data_alt = DataAlt dc argIds
                            sym_fun_ty = mkTyFun $ fst (argTypes dcty) ++ [t2]
                            (fi, ng1'') = freshSeededId (Name "symFun" Nothing 0 Nothing) sym_fun_ty ng1'
                            vargs = map Var argIds
                        in (Alt data_alt (mkApp (Var fi : vargs)) : as, fi : sids, ng1'')
                        ) ([], [], ng'') dcs
        -- alts = map (\dc -> Alt (Alt)) dcs
        e = Lam TermL x $ Case (Tick (dc_split_tick sft) (Var x)) x' t2 alts
        e' = mkApp (e:es)
        eenv' = foldr E.insertSymbolic eenv symIds
        eenv'' = E.insert n e eenv'
        (constState, ng'''') = mkFuncConst sft s es n t1 t2 ng'''
    in Just (RuleReturnReplaceSymbFunc, [constState, s {
        curr_expr = CurrExpr Evaluate e',
        expr_env = eenv''
    }], ng'''')

    -- FUNC-APP
    | Var (Id n (TyFun t1@(TyFun _ _) t2)):es <- unApp ce
    , E.isSymbolic n eenv
    = let
        (tfs, tr) = argTypes t1
        (xIds, ng') = freshIds tfs ng
        xs = map Var xIds
        (fId, ng'') = freshId (TyFun tr $ TyFun t1 t2) ng'
        f = Var fId
        (fa, ng''') = freshId t1 ng''
        e = Lam TermL fa . Tick (func_split_tick sft) $ mkApp [f, mkApp (Var fa : xs), Var fa]
        eenv' = foldr E.insertSymbolic eenv xIds
        -- eenv'' = E.insertSymbolic (idName fId) fId eenv'
        eenv'' = E.insertSymbolic fId eenv'
        eenv''' = E.insert n e eenv''
        (constState, ng'''') = mkFuncConst sft s es n t1 t2 ng'''
    in Just (RuleReturnReplaceSymbFunc, [constState, s {
        curr_expr = CurrExpr Evaluate $ mkApp (e:es),
        expr_env = eenv'''
    }], ng'''')

    -- LIT-SPLIT
    | Var (Id n (TyFun t1 t2)):ea:es <- unApp ce
    , isPrimType t1
    , E.isSymbolic n eenv
    = let
        boolTy = (TyCon (KV.tyBool kv) TYPE)
        trueDc = DataCon (KV.dcTrue kv) boolTy [] []
        falseDc = DataCon (KV.dcFalse kv) boolTy [] []
        eqT1 = mkEqPrimType t1 kv
        (f1Id:f2Id:xId:discrimId:[], ng') = freshIds [t2, TyFun t1 t2, t1, boolTy] ng
        x = Var xId
        e = Lam TermL xId $ Case (Tick (lit_split_tick sft) (mkApp [eqT1, x, ea])) discrimId t2
           [ Alt (DataAlt trueDc []) (Var f1Id)
           , Alt (DataAlt falseDc []) (App (Var f2Id) x)]
        eenv' = foldr E.insertSymbolic eenv [f1Id, f2Id]
        eenv'' = E.insert n e eenv'
    in Just (RuleReturnReplaceSymbFunc, [s {
        -- because we are always going down true branch
        curr_expr = CurrExpr Evaluate (mkApp (Var f1Id:es)),
        expr_env = eenv''
    }], ng')
    | otherwise = Nothing

argTypes :: Type -> ([Type], Type)
argTypes t = (anonArgumentTypes t, returnType t)

genArgIds :: DataCon -> NameGen -> ([Id], NameGen)
genArgIds (DataCon _ dcty _ _) ng =
    let (argTys, _) = argTypes dcty
    in foldr (\ty (is, ng') -> let (i, ng'') = freshId ty ng' in ((i:is), ng'')) ([], ng) argTys

mkFuncConst :: SymFuncTicks -> State t -> [Expr] -> Name -> Type -> Type -> NameGen -> (State t, NameGen)
mkFuncConst sft s@(State { expr_env = eenv } ) es n t1 t2 ng =
    let
        (fId:xId:[], ng') = freshIds [t2, t1] ng
        eenv' = foldr E.insertSymbolic eenv [fId]
        e = Lam TermL xId . Tick (const_tick sft) $ Var fId
        eenv'' = E.insert n e eenv'
    in (s {
        curr_expr = CurrExpr Evaluate $ mkApp (e:es),
        -- symbolic_ids = fId:symbolic_ids state,
        expr_env = eenv''
    }, ng')

-- If the expression is a symbolic higher order function application, replaces
-- it with a symbolic variable of the correct type.
-- A non reduced path constraint is added, to force solving for the symbolic
-- function later.
retReplaceSymbFuncVar :: SymFuncTicks ->  State t -> NameGen -> Expr -> Maybe (Rule, [State t], NameGen)
retReplaceSymbFuncVar _
                      s@(State { expr_env = eenv
                               , exec_stack = stck 
                               , tyvar_env = tvnv})
                      ng ce
    | notApplyFrame
    , (Var (Id f idt):_) <- unApp ce
    , E.isSymbolic f eenv
    , isTyFun idt
    , t <- typeOf tvnv ce
    , not (isTyFun t) =
        let
            (new_sym, ng') = freshSeededString "sym" ng
            new_sym_id = Id new_sym t
            nrpc' = non_red_path_conds s S.:|> (ce, Var new_sym_id)
        in
        Just (RuleReturnReplaceSymbFunc, 
            [s { expr_env = E.insertSymbolic new_sym_id eenv
               , curr_expr = CurrExpr Return (Var new_sym_id)
               , non_red_path_conds = nrpc' }]
            , ng')
    | otherwise = Nothing
    where
        notApplyFrame | Just (frm, _) <- S.pop stck = not (isApplyFrame frm)
                      | otherwise = True

isApplyFrame :: Frame -> Bool
isApplyFrame (ApplyFrame _) = True
isApplyFrame _ = False
