-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Rules
  ( Rule (..)
  , isExecValueForm
  , stackReduce
  ) where

import G2.Internals.Language
import G2.Internals.Language.Stack
import qualified G2.Internals.Language.ExprEnv as E


data Rule = RuleEvalVal
          | RuleEvalVarNonVal | RuleEvalVarVal
          | RuleEvalUnInt
          | RuleEvalApp
          | RuleEvalLet
          | RuleEvalCaseData | RuleEvalCaseLit | RuleEvalCaseDefault
                             | RuleCaseSym | RuleEvalCaseNonVal

          | RuleReturnUpdateVar | RuleReturnUpdateNonVar
          | RuleReturnCase
          | RuleReturnApplyLam | RuleReturnApplyData
                                  | RuleReturnApplySym

          | RuleIdentity

          | RuleError
           deriving (Show, Eq, Read)

-- | Check whether or not a value is the result of symbolic application. This
-- would require us to go through a chain of things to make sure that the LHS
-- of the sequence of Apps is mapped to a Nothing -- effectively a normal form.
isSymbolic :: Id -> E.ExprEnv -> Bool
isSymbolic var eenv = case E.lookup (idName var) eenv of
    Just (App (Var fvar) _) -> isSymbolic fvar eenv
    Just _ -> False
    Nothing -> True

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

-- | If something is in "value form", then it is essentially ready to be
-- returned and popped off the heap. This will be the SSTG equivalent of having
-- Return vs Evaluate for the ExecCode of the `State`.
--
-- So in this context, the following are considered NOT-value forms:
--   `Var`, only if a lookup still available in the expression environment.
--   `App`, which involves pushing the RHS onto the `Stack`.
--   `Let`, which involves binding the binds into the eenv
--   `Case`, which involves pattern decomposition and stuff.
isExprValueForm :: Expr -> E.ExprEnv -> Bool
isExprValueForm (Var var) eenv =
    E.lookup (idName var) eenv == Nothing || isSymbolic var eenv
isExprValueForm (App f a) _ = case unApp (App f a) of
    (Data _:_) -> True
    _ -> False
isExprValueForm (Let _ _) _ = False
isExprValueForm (Case _ _ _) _ = False
isExprValueForm _ _ = True

-- | Is the execution state in a value form of some sort? This would entail:
-- * The `Stack` is empty.
-- * The `ExecCode` is in a `Return` form.
isExecValueForm :: State -> Bool
isExecValueForm state | Nothing <- pop (stack state)
                      , CurrExpr Return _ <- curr_expr state = True

                      | otherwise = False

-- | Rename multiple things at once with [(olds, news)] on a `Renameable`.
renamings :: Renamable a => [(Name, Name)] -> a -> a
renamings names a = foldr (\(old, new) -> renaming old new) a names

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
           (E.ExprEnv, Expr, NameGen)
liftBinds kvs eenv expr ngen = (eenv', expr', ngen')
  where
    olds = map (idName . fst) kvs
    (news, ngen') = freshSeededNames olds ngen
    eenv' = E.insertExprs (zip news (map snd kvs)) eenv
    expr' = renamings (zip olds news) expr

-- | `DataCon` `Alt`s.
dataAlts :: [Alt] -> [(DataCon, [Id], Expr)]
dataAlts alts = [(dcon, ps, aexpr) | Alt (DataAlt dcon ps) aexpr <- alts]

-- | `Lit` `Alt`s.
litAlts :: [Alt] -> [(Lit, Expr)]
litAlts alts = [(lit, aexpr) | Alt (LitAlt lit) aexpr <- alts]

-- | DEFAULT `Alt`s.
defaultAlts :: [Alt] -> [Alt]
defaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts dc alts = [a | a @ (Alt (DataAlt adc _) _) <- alts , dc == adc]

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

-- | Negate an `PathCond`.
negatePathCond :: PathCond -> PathCond
negatePathCond (AltCond a e b) = AltCond a e (not b)
negatePathCond (ExtCond e b) = ExtCond e (not b)

-- | Lift positive datacon `State`s from symbolic alt matching. This in
-- part involves erasing all of the parameters from the environment by renaming
-- their occurrence in the aexpr to something fresh.
liftSymDataAlt :: State -> Expr -> (DataCon, [Id], Expr) -> Id ->
                  (State, PathCond)
liftSymDataAlt state mexpr (dcon, params, aexpr) cvar = (state', cond)
  where
    eenv = expr_env state
    paths = path_conds state
    ngen = name_gen state
    -- Condition that was matched.
    cond = AltCond (DataAlt dcon params) mexpr True
    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params
    (aexpr', ngen') = rename' olds ngen aexpr
    -- Now do a round of renaming for binding the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr'', ngen'') = liftBinds binds eenv aexpr' ngen'
    state' = state { expr_env = eenv'
                   , curr_expr = CurrExpr Evaluate aexpr''
                   , path_conds = cond : paths
                   , name_gen = ngen'' }

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt :: State -> Expr -> (Lit, Expr) -> Id -> (State, PathCond)
liftSymLitAlt state mexpr (lit, aexpr) cvar = (state', cond)
  where
    eenv = expr_env state
    paths = path_conds state
    ngen = name_gen state
    -- Condition that was matched.
    cond = AltCond (LitAlt lit) mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    (eenv', aexpr', ngen') = liftBinds binds eenv aexpr ngen
    state' = state { expr_env = eenv'
                   , curr_expr = CurrExpr Evaluate aexpr'
                   , path_conds = cond : paths
                   , name_gen = ngen' }

-- | Lift default alts found in symbolic case matching.
liftSymDefAlt :: State -> Expr -> [PathCond] -> Expr -> Id -> State
liftSymDefAlt state mexpr negatives aexpr cvar = state'
  where
    eenv = expr_env state
    paths = path_conds state
    ngen = name_gen state
    -- Bind the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr', ngen') = liftBinds binds eenv aexpr ngen
    state' = state { expr_env = eenv'
                   , curr_expr = CurrExpr Evaluate aexpr'
                   , path_conds = negatives ++ paths
                   , name_gen = ngen' }

-- | Funciton for performing rule reductions based on stack based evaluation
-- semantics with heap memoization.
stackReduce :: State -> (Rule, [State])
stackReduce state @ State { stack = stack
                          , expr_env = eenv
                          , curr_expr = code
                          , name_gen = ngen
                          , path_conds = paths }

-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)

    -- Our current thing is a value form, which means we can return it.
    | CurrExpr Evaluate expr <- code
    , isExprValueForm expr eenv =
        ( RuleEvalVal
        , [state { curr_expr = CurrExpr Return expr }])

    -- If our variable points to something on the heap, we first push the
    -- current name of the variable onto the stack and evaluate the expression
    -- that it points to only if it is not a value. After the latter is done
    -- evaluating, we pop the stack to add a redirection pointer into the heap.
    | CurrExpr Evaluate (Var var) <- code
    , Just expr <- E.lookup (idName var) eenv
    , not (isExprValueForm expr eenv) =
        let frame = UpdateFrame (idName var)
        in ( RuleEvalVarNonVal
           , [state { stack = push frame stack
                    , curr_expr = CurrExpr Evaluate expr }])

    -- If the target in our environment is already a value form, we do not
    -- need to push additional redirects for updating later on.
    | CurrExpr Evaluate (Var var) <- code
    , Just expr <- E.lookup (idName var) eenv
    , isExprValueForm expr eenv =
        ( RuleEvalVarVal
        , [state { curr_expr = CurrExpr Evaluate expr }])

    -- Push application RHS onto the stack. This is essentially the same as the
    -- original STG rules, but we pretend that every function is (appropriately)
    -- single argument. However one problem is that eenv sharing has a redundant
    -- representation because long `App` chains will all share the same eenv.
    -- However given actual lazy evaluations within Haskell, all the
    -- `ExecExprEnv`s at each frame would really be stored in a single
    -- location on the actual Haskell heap during execution.
    | CurrExpr Evaluate (App fexpr aexpr) <- code =
        let frame = ApplyFrame aexpr
        in ( RuleEvalApp
           , [state { stack = push frame stack
                    , curr_expr = CurrExpr Evaluate fexpr }])

    -- Lift all the let bindings into the environment and continue with eenv
    -- and continue with evaluation of the let expression.
    | CurrExpr Evaluate (Let binds expr) <- code =
        let (eenv', expr', ngen') = liftBinds binds eenv expr ngen
        in ( RuleEvalLet
           , [state { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate expr'
                    , name_gen = ngen' }])

    -- | Is the current expression able to match with a literal based `Alt`? If
    -- so, we do the cvar binding, and proceed with evaluation of the body.
    | CurrExpr Evaluate (Case (Lit lit) cvar alts) <- code
    , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
        let binds = [(cvar, Lit lit)]
            (eenv', expr', ngen') = liftBinds binds eenv expr ngen
        in ( RuleEvalCaseLit
           , [state { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate expr'
                    , name_gen = ngen' }])

    -- Is the current expression able to match a data consturctor based `Alt`?
    -- If so, then we bind all the parameters to the appropriate arguments and
    -- proceed with the evaluation of the `Alt`'s expression. We also make sure
    -- to perform the cvar binding.
    | CurrExpr Evaluate (Case mexpr cvar alts) <- code
    , (Data dcon):args <- unApp mexpr
    , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
    , length params == length args =
        let binds = (cvar, mexpr) : zip params args
            (eenv', expr', ngen') = liftBinds binds eenv expr ngen
        in ( RuleEvalCaseData
           , [state { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate expr'
                    , name_gen = ngen' }])

    -- | We are not able to match any of the stuff, and hit a DEFAULT instead?
    -- If so, we just perform the cvar binding and proceed with the alt
    -- expression.
    | CurrExpr Evaluate (Case mexpr cvar alts) <- code
    , (Alt _ expr):_ <- defaultAlts alts =
        let binds = [(cvar, mexpr)]
            (eenv', expr', ngen') = liftBinds binds eenv expr ngen
        in ( RuleEvalCaseDefault
           , [state { expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate expr'
                    , name_gen = ngen' }])

    -- | If we are pointing to a symbolic value in the environment, handle it
    -- appropriately by branching on every `Alt`.
    | CurrExpr Evaluate (Case (Var var) cvar alts) <- code
    , isSymbolic var eenv
    , (dalts, lalts, defs) <- (dataAlts alts, litAlts alts, defaultAlts alts)
    , (length dalts + length lalts + length defs) > 0 =
        let dsts_cs = map (\d -> liftSymDataAlt state (Var var) d cvar) dalts
            lsts_cs = map (\l -> liftSymLitAlt state (Var var) l cvar) lalts
            (data_sts, dconds) = unzip dsts_cs
            (lit_sts, lconds) = unzip lsts_cs
            negs = map negatePathCond (dconds ++ lconds)
            def_sts = map (\(Alt _ aexpr) ->
                           liftSymDefAlt state (Var var) negs aexpr cvar) defs
        in (RuleCaseSym, data_sts ++ lit_sts ++ def_sts)

    -- Case evaluation also uses the stack in graph reduction based evaluation
    -- semantics. The case's binding variable and alts are pushed onto the stack
    -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
    -- is only done when the matching expression is NOT in value form. Value
    -- forms should be handled by other RuleEvalCase* rules.
    | CurrExpr Evaluate (Case mexpr cvar alts) <- code
    , not (isExprValueForm mexpr eenv) =
        let frame = CaseFrame cvar alts
        in ( RuleEvalCaseNonVal
           , [state { stack = push frame stack
                    , curr_expr = CurrExpr Evaluate mexpr }])

    -- Return forms the `ExecCode`.

    -- We are returning something and the first thing that we have on the stack
    -- is an `UpdateFrame`, this means that we add a redirection pointer to the
    -- `ExecExprEnv`, and continue with execution. This is the equivalent of
    -- performing memoization on values that we have seen.
    | Just (UpdateFrame frm_name, stack') <- pop stack
    , CurrExpr Return (Var (Id name ty)) <- code =
        ( RuleReturnUpdateVar
        , [state { stack = stack'
                 , expr_env = E.redirect frm_name name eenv
                 , curr_expr = CurrExpr Return (Var (Id name ty)) }])

    -- If the variable we are returning does not have a `Var` in it at the
    -- immediate top level, then we have to insert it into the `ExecExprEnv`
    -- directly.
    | Just (UpdateFrame frm_name, stack') <- pop stack
    , CurrExpr Return expr <- code =
        ( RuleReturnUpdateNonVar
        , [state { stack = stack'
                 , expr_env = E.insert frm_name expr eenv
                 , curr_expr = CurrExpr Return expr }])

    -- In the event that we are returning and we have a `CaseFrame` waiting for
    -- us at the top of the stack, we would simply inject it into the case
    -- expression. We do some assumptions here about the form of expressions!
    | Just (CaseFrame cvar alts, stack') <- pop stack
    , CurrExpr Return expr <- code =
        ( RuleReturnCase
        , [state { stack = stack'
                 , curr_expr = CurrExpr Evaluate (Case expr cvar alts) }])

    -- When we have an `ApplyFrame` on the top of the stack, things might get a
    -- bit tricky, since we need to make sure that the thing we end up returning
    -- is appropriately a value. In the case of `Lam`, we need to perform
    -- application, and then go into the expression body.
    | Just (ApplyFrame aexpr, stack') <- pop stack
    , CurrExpr Return (Lam b lexpr) <- code =
        let binds = [(b, aexpr)]
            (eenv', lexpr', ngen') = liftBinds binds eenv lexpr ngen
        in ( RuleReturnApplyLam
           , [state { stack = stack'
                    , expr_env = eenv'
                    , curr_expr = CurrExpr Evaluate lexpr'
                    , name_gen = ngen' }])

    -- When we have an `DataCon` application chain, we need to tack on the
    -- expression in the `ApplyFrame` at the end.
    | Just (ApplyFrame aexpr, stack') <- pop stack
    , CurrExpr Return dexpr <- code
    , (Data _):_ <- unApp dexpr =
        ( RuleReturnApplyData
        , [state { stack = stack'
                 , expr_env = eenv
                 , curr_expr = CurrExpr Return (App dexpr aexpr) }])

  -- When we return symbolic values on an `ApplyFrame`, introduce new name
  -- mappings in the eenv to form this long symbolic normal form chain.
  | Just (ApplyFrame aexpr, stack') <- pop stack
  , CurrExpr Return (Var var) <- code
  , isSymbolic var eenv =
      let (sname, ngen') = freshSeededName (idName var) ngen
          sym_app = App (Var var) aexpr
          svar = Id sname (TyApp (typeOf var) (typeOf aexpr))
      in ( RuleReturnApplySym
         , [state { stack = stack'
                  , expr_env = E.insert sname sym_app eenv
                  , curr_expr = CurrExpr Return (Var svar)
                  , name_gen = ngen' }])

    -- Our evaluation has hit a value.
    | isExecValueForm state = (RuleIdentity, [state])

    | otherwise = (RuleError, [state]) -- TODO: SET THIS BACK TO RETURN []

