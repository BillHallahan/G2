-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Rules
  ( Rule (..)
  , isExecValueForm
  , reduce
  ) where

import G2.Internals.Language
import G2.Internals.Language.Stack
import qualified G2.Internals.Language.ExprEnv as E

import Data.List
import Data.Maybe

data Rule = RuleEvalVal
          | RuleEvalVarNonVal | RuleEvalVarVal
          | RuleEvalUnInt
          | RuleEvalApp
          | RuleEvalPrimAlreadyNorm
          | RuleEvalPrimToNorm
          | RuleEvalLet
          | RuleEvalCaseData | RuleEvalCaseLit | RuleEvalCaseDefault
                             | RuleCaseSym | RuleEvalCasePrim | RuleEvalCaseNonVal
          | RuleEvalAssume | RuleEvalAssert

          | RuleReturnEUpdateVar | RuleReturnEUpdateNonVar
          | RuleReturnECase
          | RuleReturnEApplyLam | RuleReturnEApplyData
                                | RuleReturnEApplySym

          | RuleReturnCAssume | RuleEvalCAssert

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

-- | Ravels the application spine
mkApp :: [Expr] -> Expr
mkApp [] = error "mkApp: empty list"
mkApp (e:[]) = e
mkApp (e1:e2:es) = mkApp (App e1 e2 : es)


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
isExprValueForm (App f a) eenv = case unApp (App f a) of
    (Prim _ _:xs) -> all (flip isExprValueForm eenv) xs
    (Data _:xs) -> True
    (v@(Var _):xs) -> isExprValueForm v eenv
    _ -> False
isExprValueForm (Let _ _) _ = False
isExprValueForm (Case _ _ _) _ = False
isExprValueForm (Assume _ _) _ = False
isExprValueForm (Assert _ _) _ = False
isExprValueForm _ _ = True

-- | Is the execution state in a value form of some sort? This would entail:
-- * The `Stack` is empty.
-- * The `ExecCode` is in a `Return` form.
isExecValueForm :: State -> Bool
isExecValueForm state | Nothing <- pop (exec_stack state)
                      , CurrExpr Return _ <- curr_expr state = True

                      | otherwise = False

-- | Rename multiple things at once with [(olds, news)] on a `Renameable`.
renames :: Renamable a => [(Name, Name)] -> a -> a
renames names a = foldr (\(old, new) -> rename old new) a names

-- | Inject binds into the eenv. The LHS of the [(Id, Expr)] are treated as
-- seed values for the names.
liftBinds :: [(Id, Expr)] -> E.ExprEnv -> Expr -> NameGen ->
             (E.ExprEnv, Expr, NameGen)
liftBinds kvs eenv expr ngen = (eenv', expr', ngen')
  where
    olds = map (idName . fst) kvs
    (news, ngen') = freshSeededNames olds ngen
    eenv' = E.insertExprs (zip news (map snd kvs)) eenv
    expr' = renames (zip olds news) expr

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
negatePathCond (PCExists i) = PCExists i

-- | Lift positive datacon `State`s from symbolic alt matching. This in
-- part involves erasing all of the parameters from the environment by rename
-- their occurrence in the aexpr to something fresh.
liftSymDataAlt :: E.ExprEnv -> Expr -> NameGen -> Id -> [(DataCon, [Id], Expr)] -> [EvaluateResult]
liftSymDataAlt eenv mexpr ngen cvar = map (liftSymDataAlt' eenv mexpr ngen cvar)

liftSymDataAlt' :: E.ExprEnv -> Expr -> NameGen -> Id -> (DataCon, [Id], Expr) -> EvaluateResult
liftSymDataAlt' eenv mexpr ngen cvar (dcon, params, aexpr) = res
  where
    -- Condition that was matched.
    cond = AltCond (DataAlt dcon params) mexpr True
    -- Make sure that the parameters do not conflict in their symbolic reps.
    olds = map idName params
    ((cond', aexpr'), ngen') = doRenames olds ngen (cond, aexpr)
    -- Now do a round of rename for binding the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr'', ngen'') = liftBinds binds eenv aexpr' ngen'
    res = ( eenv'
          , CurrExpr Evaluate aexpr''
          , [cond']
          , ngen''
          , Nothing)

liftSymLitAlt :: E.ExprEnv -> Expr -> NameGen -> Id -> [(Lit, Expr)] -> [EvaluateResult]
liftSymLitAlt eenv mexpr ngen cvar = map (liftSymLitAlt' eenv mexpr ngen cvar)

-- | Lift literal alts found in symbolic case matching.
liftSymLitAlt' :: E.ExprEnv -> Expr -> NameGen -> Id -> (Lit, Expr) -> EvaluateResult
liftSymLitAlt' eenv mexpr ngen cvar (lit, aexpr) = res
  where
    -- Condition that was matched.
    cond = AltCond (LitAlt lit) mexpr True
    -- Bind the cvar.
    binds = [(cvar, Lit lit)]
    (eenv', aexpr', ngen') = liftBinds binds eenv aexpr ngen
    res = ( eenv'
          , CurrExpr Evaluate aexpr'
          , [cond]
          , ngen'
          , Nothing)

liftSymDefAlt :: E.ExprEnv -> Expr -> NameGen -> [PathCond] ->  Id -> [Alt] -> [EvaluateResult]
liftSymDefAlt eenv mexpr ngen negatives cvar = map (liftSymDefAlt' eenv mexpr ngen negatives cvar)

-- | Lift default alts found in symbolic case matching.
liftSymDefAlt' :: E.ExprEnv -> Expr -> NameGen -> [PathCond] ->  Id -> Alt -> EvaluateResult
liftSymDefAlt' eenv mexpr ngen negatives cvar (Alt _ aexpr) = res
  where
    -- Bind the cvar.
    binds = [(cvar, mexpr)]
    (eenv', aexpr', ngen') = liftBinds binds eenv aexpr ngen
    res = ( eenv'
          , CurrExpr Evaluate aexpr'
          , negatives
          , ngen'
          , Nothing)

-- | Attempts to reduce a Var from the eenv.
varReduce :: E.ExprEnv -> Expr -> Expr
varReduce eenv (Var i) = fromMaybe (Var i) (return . varReduce eenv =<< E.lookup (idName i) eenv)
varReduce _ e = e

-- | Funciton for performing rule reductions based on stack based evaluation
-- semantics with heap memoization.

-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)

reduce :: State -> (Rule, [State])
reduce s @ State { exec_stack = estk
                 , expr_env = eenv
                 , curr_expr = cexpr
                 , name_gen = ngen
                 , path_conds = paths }
  | isExecValueForm s =
      (RuleIdentity, [s])

  | CurrExpr Evaluate expr <- cexpr
  , isExprValueForm expr eenv =
      -- Our current thing is a value form, which means we can return it.
      (RuleEvalVal, [s { curr_expr = CurrExpr Return expr }])

  | CurrExpr Evaluate expr <- cexpr =
      let (rule, eval_results) = reduceEvaluate eenv expr ngen
          states = map (\(eenv', cexpr', paths', ngen', f) ->
                         s { expr_env = eenv'
                           , curr_expr = cexpr'
                           , path_conds = paths' ++ paths
                           , name_gen = ngen'
                           , exec_stack = maybe estk (\f' -> push f' estk) f})
                       eval_results
      in (rule, states)

  | CurrExpr Return expr <- cexpr
  , Just (AssumeFrame fexpr, estk') <- pop estk =
      let cond = ExtCond expr True
      in ( RuleReturnCAssume
         , [s { exec_stack = estk'
              , curr_expr = CurrExpr Evaluate fexpr
              , path_conds = cond : paths }])

  | CurrExpr Return expr <- cexpr
  , Just (f, estk') <- pop estk =
      let (rule, (eenv', cexpr', ngen')) = reduceEReturn eenv expr ngen f
      in (rule, [s { expr_env = eenv'
                   , curr_expr = cexpr'
                   , name_gen = ngen'
                   , exec_stack = estk' }])

  | otherwise = (RuleError, [s])

-- | Result of a Evaluate reduction.
type EvaluateResult = (E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)

-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)
reduceEvaluate :: E.ExprEnv -> Expr -> NameGen -> (Rule, [EvaluateResult])
reduceEvaluate eenv (Var var) ngen = case E.lookup (idName var) eenv of
    Just expr ->
      -- If the target in our environment is already a value form, we do not
      -- need to push additional redirects for updating later on.
      if isExprValueForm expr eenv
        then ( RuleEvalVarVal
             , [( eenv
                , CurrExpr Evaluate expr
                , []
                , ngen
                , Nothing)])

        -- If our variable points to something on the heap, we first push the
        -- current name of the variable onto the stack and evaluate the
        -- expression that it points to only if it is not a value. After the
        -- latter is done evaluating, we pop the stack to add a redirection
        -- pointer into the heap.
        else let frame = UpdateFrame (idName var)
             in ( RuleEvalVarNonVal
                , [( eenv
                   , CurrExpr Evaluate expr
                   , []
                   , ngen
                   , Just frame)])
    Nothing -> error "reduceEvaluate: lookup was Nothing"

reduceEvaluate eenv (App fexpr aexpr) ngen =
    -- Push application RHS onto the stack. This is essentially the same as the
    -- original STG rules, but we pretend that every function is (appropriately)
    -- single argument. However one problem is that eenv sharing has a redundant
    -- representation because long `App` chains will all share the same eenv.
    -- However given actual lazy evaluations within Haskell, all the
    -- `ExecExprEnv`s at each frame would really be stored in a single
    -- location on the actual Haskell heap during execution.
    case unApp (App fexpr aexpr) of
        ((Prim prim ty):args) ->
            let args' = map (varReduce eenv) args
            in ( RuleEvalPrimToNorm
                , [( eenv
                   -- This may need to be Evaluate if there are more
                   -- than one redirections.
                   , CurrExpr Evaluate (mkApp (Prim prim ty : args'))
                   , []
                   , ngen
                   , Nothing)])
        _ ->
            let frame = ApplyFrame aexpr
            in ( RuleEvalApp
               , [( eenv
                  , CurrExpr Evaluate fexpr
                  , []
                  , ngen
                  , Just frame)])

reduceEvaluate eenv (Let binds expr) ngen =
    -- Lift all the let bindings into the environment and continue with eenv
    -- and continue with evaluation of the let expression.
    let (eenv', expr', ngen') = liftBinds binds eenv expr ngen
    in ( RuleEvalLet
       , [( eenv'
          , CurrExpr Evaluate expr'
          , []
          , ngen'
          , Nothing)])

reduceEvaluate eenv (Case mexpr cvar alts) ngen =
    reduceCase eenv mexpr cvar alts ngen

reduceEvaluate eenv (Assume pre lexpr) ngen =
    let frame = AssumeFrame lexpr
    in (RuleEvalAssume, [( eenv
                         , CurrExpr Evaluate pre
                         , []
                         , ngen
                         , Just frame)])
reduceEvaluate eenv (Assert pre lexpr) ngen =
    (RuleEvalCAssert, [( eenv
                         , CurrExpr Evaluate (Assume (App (mkNot eenv) pre) lexpr)
                         , []
                         , ngen
                         , Nothing)])

reduceEvaluate eenv c ngen =
    (RuleError, [(eenv, CurrExpr Evaluate c, [], ngen, Nothing)])

-- | Result of a Case reduction.
type CaseResult = [(E.ExprEnv, CurrExpr, [PathCond], NameGen, Maybe Frame)]

-- | Handle the Case forms of Evaluate.
reduceCase :: E.ExprEnv -> Expr -> Id -> [Alt] -> NameGen -> (Rule, CaseResult)
reduceCase eenv mexpr bind alts ngen
  -- | Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | (Lit lit) <- mexpr
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
      let binds = [(bind, Lit lit)]
          (eenv', expr', ngen') = liftBinds binds eenv expr ngen
      in ( RuleEvalCaseLit
         , [( eenv'
            , CurrExpr Evaluate expr'
            , []
            , ngen'
            , Nothing)])

  -- Is the current expression able to match a data consturctor based `Alt`?
  -- If so, then we bind all the parameters to the appropriate arguments and
  -- proceed with the evaluation of the `Alt`'s expression. We also make sure
  -- to perform the cvar binding.
  | (Data dcon):args <- unApp mexpr
  , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
  , length params == length args =
      let binds = (bind, mexpr) : zip params args
          (eenv', expr', ngen') = liftBinds binds eenv expr ngen
      in ( RuleEvalCaseData
         , [( eenv'
            , CurrExpr Evaluate expr'
            , []
            , ngen'
            , Nothing)] )

  -- | If we are pointing to a symbolic value in the environment, handle it
  -- appropriately by branching on every `Alt`.
  | var@(Var n) <- mexpr
  , isSymbolic n eenv
  , dalts <- dataAlts alts
  , lalts <- litAlts alts
  , defs <- defaultAlts alts
  , (length dalts + length lalts + length defs) > 0 =
      let dsts_cs = liftSymDataAlt eenv var ngen bind dalts
          lsts_cs = liftSymLitAlt eenv var ngen bind lalts
          (_, _, dconds, _, _) = unzip5 dsts_cs
          (_, _, lconds, _, _) = unzip5 lsts_cs
          negs = map (negatePathCond) $ concat (dconds ++ lconds)
          def_sts = liftSymDefAlt eenv var ngen negs bind defs
      in (RuleCaseSym, dsts_cs ++ lsts_cs ++ def_sts)

  -- We bind value form primitive applications to a new var.  This allows
  -- RuleCaseSym to run in the next call to reduce.
  -- | (Prim _ t:_) <- unApp mexpr =
  --   let
  --       (n, ngen') = freshName ngen
  --       t' = returnType t
  --       mexpr' = Var $ Id n t'
  --   in (RuleEvalCasePrim
  --      , [( eenv
  --         , CurrExpr Evaluate mexpr'
  --         , []
  --         , ngen'
  --         , Nothing)])


  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `ExecExprEnv`. However this
  -- is only done when the matching expression is NOT in value form. Value
  -- forms should be handled by other RuleEvalCase* rules.
  | not (isExprValueForm mexpr eenv) =
      let frame = CaseFrame bind alts
      in ( RuleEvalCaseNonVal
         , [( eenv
            , CurrExpr Evaluate mexpr
            , []
            , ngen
            , Just frame)])

   -- | We are not able to match any of the stuff, and hit a DEFAULT instead?
  -- If so, we just perform the cvar binding and proceed with the alt
  -- expression.
  | (Alt _ expr):_ <- defaultAlts alts =
      let binds = [(bind, mexpr)]
          (eenv', expr', ngen') = liftBinds binds eenv expr ngen
      in ( RuleEvalCaseDefault
         , [( eenv'
            , CurrExpr Evaluate expr'
            , []
            , ngen'
            , Nothing)])
 
  | otherwise = error $ "reduceCase: bad case passed in\n" ++ show mexpr ++ "\n" ++ show alts

-- | Result of a Return reduction.
type EReturnResult = (E.ExprEnv, CurrExpr, NameGen)

-- | Handle the Return states.
reduceEReturn :: E.ExprEnv -> Expr -> NameGen -> Frame -> (Rule, EReturnResult)

-- We are returning something and the first thing that we have on the stack
-- is an `UpdateFrame`, this means that we add a redirection pointer to the
-- `ExecExprEnv`, and continue with execution. This is the equivalent of
-- performing memoization on values that we have seen.
reduceEReturn eenv (Var (Id name ty)) ngen (UpdateFrame frm_name) =
  ( RuleReturnEUpdateVar
  , ( E.redirect frm_name name eenv
    , CurrExpr Return (Var $ Id name ty)
    , ngen))

-- If the variable we are returning does not have a `Var` in it at the
-- immediate top level, then we have to insert it into the `ExecExprEnv`
-- directly.
reduceEReturn eenv expr ngen (UpdateFrame frm_name) =
  ( RuleReturnEUpdateNonVar
  , ( E.insert frm_name expr eenv
    , CurrExpr Return expr
    , ngen))

-- In the event that we are returning and we have a `CaseFrame` waiting for
-- us at the top of the stack, we would simply inject it into the case
-- expression. We do some assumptions here about the form of expressions!
reduceEReturn eenv expr ngen (CaseFrame cvar alts) =
  ( RuleReturnECase
  , ( eenv
    , CurrExpr Evaluate (Case expr cvar alts)
    , ngen))

-- When we have an `ApplyFrame` on the top of the stack, things might get a
-- bit tricky, since we need to make sure that the thing we end up returning
-- is appropriately a value. In the case of `Lam`, we need to perform
-- application, and then go into the expression body.
reduceEReturn eenv (Lam b lexpr) ngen (ApplyFrame aexpr) =
  let binds = [(b, aexpr)]
      (eenv', lexpr', ngen') = liftBinds binds eenv lexpr ngen
  in ( RuleReturnEApplyLam
     , ( eenv'
       , CurrExpr Evaluate lexpr'
       , ngen'))

-- When we have an `DataCon` application chain, we need to tack on the
-- expression in the `ApplyFrame` at the end.
reduceEReturn eenv dexpr@(App (Data _) _) ngen (ApplyFrame aexpr) =
  ( RuleReturnEApplyData
  , ( eenv
    , CurrExpr Return (App dexpr aexpr)
    , ngen))

-- When we return symbolic values on an `ApplyFrame`, introduce new name
-- mappings in the eenv to form this long symbolic normal form chain.
reduceEReturn eenv c@(Var var) ngen (ApplyFrame aexpr) =
  if not (isSymbolic var eenv)
    then (RuleError, (eenv, CurrExpr Return c, ngen))
    else let (sname, ngen') = freshSeededName (idName var) ngen
             sym_app = App (Var var) aexpr
             svar = Id sname (TyApp (typeOf var) (typeOf aexpr))
         in ( RuleReturnEApplySym
            , ( E.insert sname sym_app eenv
              , CurrExpr Return (Var svar)
              , ngen'))

reduceEReturn eenv c ngen _ = (RuleError, (eenv, CurrExpr Return c, ngen))

