{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.Rules2 ( module G2.Execution.RuleTypes
                           , stdReduce
                           , evalVar
                           , evalApp
                           , evalLam
                           , retLam
                           , evalLet
                           , evalCase
                           , reduceType
                           , evalCast
                           , reduceCoercion
                           , evalTick
                           , evalNonDet
                           , evalSymGen
                           , evalAssume
                           , evalAssert

                           , isExecValueForm ) where

import G2.Execution.NormalForms
import G2.Execution.PrimitiveEval
import G2.Execution.RuleTypes
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.PathConds as PC
import qualified G2.Language.Stack as S
import G2.Solver hiding (Assert)

import Control.Monad.Extra
import Data.Maybe

stdReduce :: Solver solver => solver -> State t -> IO (Rule, [(State t, ())])
stdReduce solver s = do
    (r, s') <- stdReduce' solver s
    let s'' = map (\ss -> ss { rules = r:rules ss }) s'
    return (r, zip s'' $ repeat ())

stdReduce' :: Solver solver => solver -> State t -> IO (Rule, [State t])
stdReduce' solver s@(State { curr_expr = CurrExpr Evaluate ce })
    | Var i  <- ce = return $ evalVar s i
    | App e1 e2 <- ce = return $ evalApp s e1 e2
    | Let b e <- ce = return $ evalLet s b e
    | Case e i a <- ce = do
        let (r, xs) = evalCase s e i a
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs')
    | Cast e c <- ce = return $ evalCast s e c
    | Tick t e <- ce = return $ evalTick s t e
    | NonDet es <- ce = return $ evalNonDet s es
    | SymGen t <- ce = return $ evalSymGen s t
    | Assume fc e1 e2 <- ce = return $ evalAssume s fc e1 e2
    | Assert fc e1 e2 <- ce = return $ evalAssert s fc e1 e2
    | otherwise = return (RuleReturn, [s { curr_expr = CurrExpr Return ce }])
stdReduce' solver s@(State { curr_expr = CurrExpr Return ce
                           , exec_stack = stck })
    | Prim Error _ <- ce
    , Just (_, stck') <- S.pop stck = return (RuleError, [s { exec_stack = stck' }])
    | Just (UpdateFrame n, stck') <- frstck = return $ retUpdateFrame s n stck'
    | Lam u i e <- ce = return $ retLam s u i e
    | Just (ApplyFrame e, stck') <- S.pop stck = return $ retApplyFrame s ce e stck'
    | Just rs <- retReplaceSymbFunc s ce = return rs
    | Just (CaseFrame i a, stck') <- frstck = return $ retCaseFrame s ce i a stck'
    | Just (CastFrame c, stck') <- frstck = return $ retCastFrame s ce c stck'
    | Just (AssumeFrame e, stck') <- frstck = do
        let (r, xs) = retAssumeFrame s ce e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs')
    | Just (AssertFrame ais e, stck') <- frstck = do
        let (r, xs) = retAssertFrame s ce ais e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs')
    | Just (CurrExprFrame e, stck') <- frstck = do
        let (r, xs) = retCurrExpr s ce e stck'
        xs' <- mapMaybeM (reduceNewPC solver) xs
        return (r, xs')
    | Nothing <- frstck = return (RuleIdentity, [s])
    | otherwise = error $ "stdReduce': Unknown Expr" ++ show ce ++ show (S.pop stck)
        where
            frstck = S.pop stck

data NewPC t = NewPC { state :: State t
                     , new_pcs :: [PathCond] }

newPCEmpty :: State t -> NewPC t
newPCEmpty s = NewPC { state = s, new_pcs = []}

reduceNewPC :: Solver solver => solver -> NewPC t -> IO (Maybe (State t))
reduceNewPC solver
            (NewPC { state = s@(State { known_values = kv
                                      , path_conds = spc })
                   , new_pcs = pc })
    | not (null pc) = do
        -- Optimization
        -- We replace the path_conds with only those that are directly
        -- affected by the new path constraints
        -- This allows for more efficient solving, and in some cases may
        -- change an Unknown into a SAT or UNSAT
        -- Switching which of the following two lines is commented turns this on/off
        -- let s'' = s'
        let new_pc = foldr (PC.insert kv) spc $ pc
            s' = s { path_conds = new_pc}

        let rel_pc = PC.relevant kv pc new_pc

        res <- check solver s rel_pc

        if res == SAT then
            return $ Just s'
        else
            return Nothing
    | otherwise = return  $ Just s

evalVar :: State t -> Id -> (Rule, [State t])
evalVar s@(State { expr_env = eenv
                 , exec_stack = stck })
          i
    | E.isSymbolic (idName i) eenv =
        (RuleEvalVal, [s { curr_expr = CurrExpr Return (Var i)}])
    | Just e <- E.lookup (idName i) eenv =
        -- If the target in our environment is already a value form, we do not
        -- need to push additional redirects for updating later on.
        -- If our variable is not in value form, we first push the
        -- current name of the variable onto the stack and evaluate the
        -- expression that it points to. After the evaluation,
        -- we pop the stack to add a redirection pointer into the heap.
        let
            (r, stck') = if isExprValueForm eenv e 
                           then ( RuleEvalVarVal (idName i), stck) 
                           else ( RuleEvalVarNonVal (idName i)
                                , S.push (UpdateFrame (idName i)) stck)
        in
        (r, [s { curr_expr = CurrExpr Evaluate e
               , exec_stack = stck' }])
    | otherwise = error  $ "evalVar: bad input." ++ show i

-- | If we have a primitive operator, we are at a point where either:
--    (1) We can concretely evaluate the operator, or
--    (2) We have a symbolic value, and no evaluation is possible, so we return
-- If we do not have a primitive operator, we go into the center of the apps,
-- to evaluate the function call
evalApp :: State t -> Expr -> Expr -> (Rule, [State t])
evalApp s@(State { expr_env = eenv
                 , type_env = tenv
                 , known_values = kv
                 , exec_stack = stck })
          e1 e2
    | (App (Prim BindFunc _) (Var i1)) <- e1
    , v2 <- e2 =
        ( RuleBind
        , [s { expr_env = E.insert (idName i1) v2 eenv
             , curr_expr = CurrExpr Return (mkTrue kv tenv) }])
    | isExprValueForm eenv (App e1 e2) =
        ( RuleReturnAppSWHNF
        , [s { curr_expr = CurrExpr Return (App e1 e2) }])
    | (Prim prim ty):ar <- unApp (App e1 e2) = 
        let
            ar' = map (lookupForPrim eenv) ar
            appP = mkApp (Prim prim ty : ar')
            exP = evalPrims kv tenv appP
        in
        ( RuleEvalPrimToNorm
        , [s { curr_expr = CurrExpr Return exP }])
    | otherwise =
        let
            frame = ApplyFrame e2
            stck' = S.push frame stck
        in
        ( RuleEvalApp e2
        , [s { curr_expr = CurrExpr Evaluate e1
             , exec_stack = stck' }])

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

retLam :: State t -> LamUse -> Id -> Expr -> (Rule, [State t])
retLam s@(State { expr_env = eenv
                , exec_stack = stck
                , name_gen = ng })
       u i e
    | TypeL <- u
    , Just (ApplyFrame tf, stck') <- S.pop stck =
        case traceType eenv tf of
        Just t ->
            let
                e' = retype i t e

                binds = [(i, Type t)]
                (eenv', e'', ng', news) = liftBinds binds eenv e' ng
            in
            ( RuleReturnEApplyLamType news
            , [s { expr_env = eenv'
                 , curr_expr = CurrExpr Evaluate e''
                 , name_gen = ng'
                 , exec_stack = stck' }])
        Nothing -> error "retLam: Bad type"
    | TermL <- u
    , Just (ApplyFrame ae, stck') <- S.pop stck =
        let
            binds = [(i, ae)]
            (eenv', e', ng', news) = liftBinds binds eenv e ng
        in
        ( RuleReturnEApplyLamExpr news
        , [s { expr_env = eenv'
             , curr_expr = CurrExpr Evaluate e'
             , name_gen = ng'
             , exec_stack = stck' }])
    | otherwise = error "retLam: Bad type"

traceType :: E.ExprEnv -> Expr -> Maybe Type
traceType _ (Type t) = Just t
traceType eenv (Var (Id n _)) = traceType eenv =<< E.lookup n eenv
traceType _ _ = Nothing

evalLet :: State t -> Binds -> Expr -> (Rule, [State t])
evalLet s@(State { expr_env = eenv
                   , name_gen = ng }) b e =
    let
        (b_lhs, b_rhs) = unzip b

        olds = map idName b_lhs
        (news, ng') = freshSeededNames olds ng

        e' = renameExprs (zip olds news) e
        b_rhs' = renameExprs (zip olds news) b_rhs

        eenv' = E.insertExprs (zip news b_rhs') eenv
    in
    (RuleEvalLet news, [s { expr_env = eenv'
                          , curr_expr = CurrExpr Evaluate e'
                          , name_gen = ng'}])

-- | Handle the Case forms of Evaluate.
evalCase :: State t -> Expr -> Id -> [Alt] -> (Rule, [NewPC t])
evalCase s@(State { expr_env = eenv
                  , name_gen = ng
                  , exec_stack = stck })
         mexpr bind alts
  -- Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | (Lit lit) <- unsafeElimCast mexpr
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
      let 
          binds = [(bind, Lit lit)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseLit
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }])

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
                           , curr_expr = CurrExpr Evaluate expr''
                           , name_gen = ng' }] )

  -- We are not able to match any constructor but don't have a symbolic variable?
  -- We hit a DEFAULT instead.
  -- We perform the cvar binding and proceed with the alt
  -- expression.
  | (Data _):_ <- unApp $ unsafeElimCast mexpr
  , (Alt _ expr):_ <- matchDefaultAlts alts =
      let 
          binds = [(bind, mexpr)]
          expr' = liftCaseBinds binds expr
      in ( RuleEvalCaseDefault
         , [newPCEmpty $ s { expr_env = eenv
                           , curr_expr = CurrExpr Evaluate expr' }])

  -- If we are pointing to something in expr value form, that is not addressed
  -- by some previous case, we handle it by branching on every `Alt`, and adding
  -- path constraints.
  | isExprValueForm eenv mexpr
  , dalts <- dataAlts alts
  , lalts <- litAlts alts
  , defs <- defaultAlts alts
  , (length dalts + length lalts + length defs) > 0 =
      let
          dsts_cs = liftSymDataAlt s mexpr bind dalts
          lsts_cs = liftSymLitAlt s mexpr bind lalts
          def_sts = liftSymDefAlt s mexpr bind alts
      in
      (RuleEvalCaseSym, dsts_cs ++ lsts_cs ++ def_sts)

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
                           , exec_stack = S.push frame stck }])

  | otherwise = error $ "reduceCase: bad case passed in\n" ++ show mexpr ++ "\n" ++ show alts

-- | Remove everything from an [Expr] that are actually Types.
removeTypes :: [Expr] -> E.ExprEnv -> [Expr]
removeTypes ((Type _):es) eenv = removeTypes es eenv
removeTypes ((Var (Id n ty)):es) eenv = case E.lookup n eenv of
    Just (Type _) -> removeTypes es eenv
    _ -> (Var (Id n ty)) : removeTypes es eenv
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
liftCaseBinds ((b, e):xs) expr = liftCaseBinds xs $ replaceASTs (Var b) e expr

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
liftSymDataAlt :: State t -> Expr -> Id -> [(DataCon, [Id], Expr)] -> [NewPC t]
liftSymDataAlt s mexpr cvar = map (liftSymDataAlt' s mexpr cvar)

liftSymDataAlt' :: State t -> Expr -> Id -> (DataCon, [Id], Expr) -> NewPC t
liftSymDataAlt' s@(State { expr_env = eenv 
                         , name_gen = ngen })
                mexpr cvar (dcon, params, aexpr) =
        NewPC { state = res, new_pcs = [cond'] }
  where

    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params
    -- [ChildrenNames]
    -- Optimization
    -- We use the same names repeatedly for the children of the same ADT
    -- Haskell is purely functional, so this is OK!  The children can't change
    -- Then, in the constraint solver, we can consider fewer constraints at once
    -- (see note [AltCond] in Language/PathConds.hs) 
    (news, ngen') = case exprInCasts mexpr of
        (Var (Id n _)) -> childrenNames n olds ngen
        _ -> freshSeededNames olds ngen

    newparams = map (uncurry Id) $ zip news (map typeOf params)

    -- Condition that was matched.
    cond = AltCond (DataAlt dcon newparams) mexpr True

    -- (news, ngen') = freshSeededNames olds ngen

    --Update the expr environment
    newIds = map (\(Id _ t, n) -> (n, Id n t)) (zip params news)
    eenv' = foldr (uncurry E.insertSymbolic) eenv newIds

    (cond', aexpr') = renameExprs (zip olds news) (cond, aexpr)

    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, mexpr)]
    aexpr'' = liftCaseBinds binds aexpr'
    res = s { expr_env = eenv'
            , curr_expr = CurrExpr Evaluate aexpr''
            , name_gen = ngen' }


liftSymLitAlt :: State t -> Expr -> Id -> [(Lit, Expr)] -> [NewPC t]
liftSymLitAlt s mexpr cvar = map (liftSymLitAlt' s mexpr cvar)

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt' :: State t -> Expr -> Id -> (Lit, Expr) -> NewPC t
liftSymLitAlt' s mexpr cvar (lit, aexpr) =
    NewPC { state = res, new_pcs = [cond] }
  where
    -- Condition that was matched.
    cond = AltCond (LitAlt lit) mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    aexpr' = liftCaseBinds binds aexpr
    res = s { curr_expr = CurrExpr Evaluate aexpr' }

liftSymDefAlt :: State t -> Expr ->  Id -> [Alt] -> [NewPC t]
liftSymDefAlt s mexpr cvar as =
    let
        aexpr = defAltExpr as
    in
    case aexpr of
        Just aexpr' -> liftSymDefAlt' s mexpr aexpr' cvar as
        _ -> []

liftSymDefAlt' :: State t -> Expr -> Expr -> Id -> [Alt] -> [NewPC t]
liftSymDefAlt' s mexpr aexpr cvar as =
    let
        conds = mapMaybe (liftSymDefAltPCs mexpr) (map altMatch as)

        binds = [(cvar, mexpr)]
        aexpr' = liftCaseBinds binds aexpr
    in
    [NewPC { state = s { curr_expr = CurrExpr Evaluate aexpr' }
           , new_pcs = conds }]

defAltExpr :: [Alt] -> Maybe Expr
defAltExpr [] = Nothing
defAltExpr (Alt Default e:_) = Just e
defAltExpr (_:xs) = defAltExpr xs

liftSymDefAltPCs :: Expr -> AltMatch -> Maybe PathCond
liftSymDefAltPCs mexpr (DataAlt dc _) = Just $ ConsCond dc mexpr False
liftSymDefAltPCs mexpr lit@(LitAlt _) = Just $ AltCond lit mexpr False
liftSymDefAltPCs _ Default = Nothing

reduceType :: State t -> Type -> (Rule, [State t])
reduceType = undefined

evalCast :: State t -> Expr -> Coercion -> (Rule, [State t])
evalCast s@(State { name_gen = ng
                  , exec_stack = stck }) e c
    | cast /= cast' =
        ( RuleEvalCastSplit
        , [ s { curr_expr = CurrExpr Evaluate $ simplifyCasts cast'
              , name_gen = ng' }])
    | otherwise =
        ( RuleEvalCast
        , [s { curr_expr = CurrExpr Evaluate $ simplifyCasts e
             , exec_stack = S.push frame stck}])
    where
        cast = Cast e c
        (cast', ng') = splitCast ng cast
        frame = CastFrame c

reduceCoercion :: State t -> Coercion -> (Rule, [State t])
reduceCoercion = undefined

evalTick :: State t -> Tickish -> Expr -> (Rule, [State t])
evalTick s _ e = (RuleTick, [ s { curr_expr = CurrExpr Evaluate e }])

evalNonDet :: State t -> [Expr] -> (Rule, [State t])
evalNonDet s es =
    let
        s' = map (\e -> s { curr_expr = CurrExpr Evaluate e }) es
    in
    (RuleNonDet, s')

evalSymGen :: State t -> Type -> (Rule, [State t])
evalSymGen s@( State { expr_env = eenv
                     , name_gen = ng }) t =
    let
          (n, ng') = freshSeededString "symG" ng
          i = Id n t

          eenv' = E.insertSymbolic n i eenv
    in
    (RuleSymGen, [s { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate (Var i)
                    , name_gen = ng'
                    , symbolic_ids = i:symbolic_ids s }])

evalAssume :: State t -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t])
evalAssume s@(State { exec_stack = stck }) _ e1 e2 =
    let
        fr = AssumeFrame e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssume
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }])

evalAssert :: State t -> Maybe FuncCall -> Expr -> Expr -> (Rule, [State t])
evalAssert s@(State { exec_stack = stck }) is e1 e2 =
    let
        fr = AssertFrame is e2
        stck' = S.push fr stck
    in
    ( RuleEvalAssert
    , [ s { curr_expr = CurrExpr Evaluate e1
          , exec_stack = stck' }])

retUpdateFrame :: State t -> Name -> S.Stack Frame -> (Rule, [State t])
retUpdateFrame s@(State { expr_env = eenv
                        , curr_expr = CurrExpr _ e}) un stck
    | Var i@(Id vn _) <- e =
       ( RuleReturnEUpdateVar un
       , [s { expr_env = E.redirect un vn eenv
            , curr_expr = CurrExpr Return (Var i)
            , exec_stack = stck }])
    | otherwise =
        ( RuleReturnEUpdateNonVar un
        , [s { expr_env = E.insert un e eenv
             , exec_stack = stck }])

retApplyFrame :: State t -> Expr -> Expr -> S.Stack Frame -> (Rule, [State t])
retApplyFrame s@(State { expr_env = eenv }) e1 e2 stck'
    | Var (Id n _):_ <- unApp e1
    , E.isSymbolic n eenv = 
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Return (App e1 e2)
             , exec_stack = stck' }])
    | otherwise =
        ( RuleReturnEApplySym
        , [s { curr_expr = CurrExpr Evaluate (App e1 e2)
             , exec_stack = stck' }])

retCaseFrame :: State t -> Expr -> Id -> [Alt] -> S.Stack Frame -> (Rule, [State t])
retCaseFrame s e i a stck =
    ( RuleReturnECase
    , [s { curr_expr = CurrExpr Evaluate (Case e i a)
         , exec_stack = stck }])

retCastFrame :: State t -> Expr -> Coercion -> S.Stack Frame -> (Rule, [State t])
retCastFrame s e c stck =
    ( RuleReturnCast
    , [s { curr_expr = CurrExpr Return $ simplifyCasts $ Cast e c
         , exec_stack = stck}])

retCurrExpr :: State t -> Expr -> CurrExpr -> S.Stack Frame -> (Rule, [NewPC t])
retCurrExpr s e1 e2 stck = 
    ( RuleReturnCurrExprFr
    , [NewPC { state = s { curr_expr = e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 True]}] )

retAssumeFrame :: State t -> Expr -> Expr -> S.Stack Frame -> (Rule, [NewPC t])
retAssumeFrame s e1 e2 stck =
    ( RuleReturnCAssume
    , [NewPC { state = s { curr_expr = CurrExpr Evaluate e2
                         , exec_stack = stck}
             , new_pcs = [ExtCond e1 True]}] )

retAssertFrame :: State t -> Expr -> Maybe (FuncCall) -> Expr -> S.Stack Frame -> (Rule, [NewPC t])
retAssertFrame s e1 ais e2 stck =
    let
        s' = s { curr_expr = CurrExpr Evaluate e2
               , exec_stack = stck}

        cond = [ExtCond e1 True]

        strue = NewPC { state = s'
                      , new_pcs = cond }

        sfalse = NewPC { state = s' { true_assert = True
                                    , assert_ids = ais }
                       , new_pcs = map PC.negatePC cond }
    in
    ( RuleReturnCAssert
    , [strue, sfalse] )

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen, [Name])
liftBinds binds eenv expr ngen = (eenv', expr', ngen', news)
  where
    (bindsLHS, bindsRHS) = unzip binds

    olds = map (idName) bindsLHS
    (news, ngen') = freshSeededNames olds ngen
    expr' = renameExprs (zip olds news) expr
    bindsLHS' = renameExprs (zip olds news) bindsLHS

    binds' = zip bindsLHS' bindsRHS

    eenv' = E.insertExprs (zip news (map snd binds')) eenv

-- If the expression is a symbolic higher order function application, replaces
-- it with a symbolic variable of the correct type.
-- A non reduced path constraint is added, to force solving for the symbolic
-- function later.
retReplaceSymbFunc :: State t -> Expr -> Maybe (Rule, [State t])
retReplaceSymbFunc s@(State { expr_env = eenv
                            , name_gen = ng
                            , known_values = kv
                            , type_classes = tc
                            , exec_stack = stck })
                   ce
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
            [s { expr_env = E.insertSymbolic new_sym new_sym_id eenv
               , curr_expr = CurrExpr Return (Var new_sym_id)
               , name_gen = ng'
               , symbolic_ids = new_sym_id:symbolic_ids s
               , non_red_path_conds = nrpc_e:non_red_path_conds s }])
    | otherwise = Nothing

isApplyFrame :: Frame -> Bool
isApplyFrame (ApplyFrame _) = True
isApplyFrame _ = False
