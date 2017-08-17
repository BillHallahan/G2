-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Stack.Rules
  ( stackReduce
  ) where

import G2.Internals.Language

import G2.Internals.Execution.Support

data StackRule = StkRuleEvalVal
               | StkRuleEvalVar | StkRuleEvalUnInt
               | StkRuleEvalApp
               | StkRuleEvalLet
               | StkRuleEvalCaseData | StkRuleEvalCaseLit
                                     | StkRuleEvalCaseDefault
               | StkRuleEvalCaseNonVal

               | StkRuleReturnUpdateVar | StkRuleReturnUpdateNonVar
               | StkRuleReturnCase
               | StkRuleReturnApplyLam | StkRuleReturnApplyData
                                       | StkRuleReturnApplySym

               | StkRuleIdentity
               | StkError
               deriving (Show, Eq, Read)

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

-- | If something is in "value form", then it is essentially ready to be
-- returned and popped off the heap. This will be the SSTG equivalent of having
-- Return vs Evaluate for the Code of the `State`.
--
-- So in this context, the following are considered NOT-value forms:
--   `Var`, only if a lookup still available in the expression environment.
--   `App`, which involves pushing the RHS onto the `Stack`.
--   `Let`, which involves binding the binds into the eenv
--   `Case`, which involves pattern decomposition and stuff.
isValueForm :: Expr -> Scope -> Bool
isValueForm (Var var) scope = case vlookupScope var scope of
    Just (ExprObj _) -> False
    _ -> True
isValueForm (App f a) _ = case unApp (App f a) of
  (Data _:_) -> True
  _ -> False
isValueForm (Let _ _) _ = False
isValueForm (Case _ _ _) _ = False
isValueForm _ _ = True

-- | Convert bind objects of `(Id, Expr)` pairs into `[(Name, EnvObj)]`s.
bindsToEnvObjList :: [(Id, Expr)] -> [(Name, EnvObj)]
bindsToEnvObjList kvs = map (\(k, v) -> (idName k, ExprObj v)) kvs

-- | Inject binds into the scope.
liftBinds :: [(Id, Expr)] -> Scope -> Scope
liftBinds kvs scope = insertEnvObjs eobjs scope
  where
    eobjs = map (\(k, v) -> (idName k, ExprObj v)) kvs

-- | DEFAULT `Alt`s.
defaultAlts :: [Alt] -> [Alt]
defaultAlts alts = [a | a @ (Alt Default _) <- alts]

-- | Match data constructor based `Alt`s.
matchDataAlts :: DataCon -> [Alt] -> [Alt]
matchDataAlts dc alts = [a | a @ (Alt (DataAlt adc _) _) <- alts , dc == adc]

-- | Match literal constructor based `Alt`s.
matchLitAlts :: Lit -> [Alt] -> [Alt]
matchLitAlts lit alts = [a | a @ (Alt (LitAlt alit) _) <- alts, lit == alit]

-- | Funciton for performing rule reductions based on stack based evaluation
-- semantics with heap memoization.
stackReduce :: ExecState -> (StackRule, [ExecState])
stackReduce state @ ExecState { exec_stack = stack
                              , exec_scope = scope
                              , exec_code = code
                              , exec_names = confs
                              , exec_paths = paths }


-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)

  -- Our current thing is a value form, which means we can return it.
  | Evaluate expr <- code
  , isValueForm expr scope =
    ( StkRuleEvalVal
    , [state { exec_code = Return expr }])

  -- If our variable points to something on the heap, we first push the current
  -- name of the variable onto the stack and evaluate the expression that it
  -- points to. After the latter is done evaluating, we pop the stack to add
  -- a redirection pointer into the heap.
  | Evaluate (Var var) <- code
  , Just (ExprObj expr) <- vlookupScope var scope =
    let frame = UpdateFrame (idName var)
    in ( StkRuleEvalVar
       , [state { exec_stack = pushStack frame stack
                , exec_code = Evaluate expr }])

  -- If we encounter a vairable that is in scope, we treated it as a symbolic
  -- object and subject it to uninterpreted evaluation later on. This is done
  -- by injecting it into the heap and then evaluating the same expression
  -- again. This is the essense of memoization / single-evaluation in laziness.
  | Evaluate (Var var) <- code
  , Nothing <- vlookupScope var scope =
    let (sname, re) = freshSeededName (idName var) confs
        svar = Id sname (typeOf var)
        -- Nothing denotes that this is a "base" symbolic value that is not
        -- dependent on any other expressions.
        sym = Symbol svar Nothing
    in ( StkRuleEvalUnInt
       , [state { exec_scope = insertEnvObj (idName var, SymObj sym) scope
                , exec_code = Evaluate (Var var)
                , exec_names = re}])

  -- Push application RHS onto the stack. This is essentially the same as the
  -- original STG rules, but we pretend that every function is (appropriately)
  -- single argument. However one problem is that scope sharing has a redundant
  -- representation because long `App` chains will all share the same scope.
  -- However given actual lazy evaluations within Haskell, all the `Scope`s at
  -- each frame would really be stored in a single location on the actuall
  -- Haskell heap during execution.
  | Evaluate (App fexpr aexpr) <- code =
    let frame = ApplyFrame aexpr
    in ( StkRuleEvalApp
       , [state { exec_stack = pushStack frame stack
                , exec_code = Evaluate fexpr }])

  -- Lift all the let bindings into the environment and continue with scope and
  -- continue with evaluation of the let expression.
  | Evaluate (Let binds expr) <- code =
    ( StkRuleEvalLet
    , [state { exec_scope = liftBinds binds scope
             , exec_code = Evaluate expr }])

  -- Is the current expression able to match a data consturctor based `Alt`? If
  -- so, then we bind all the parameters to the appropriate arguments and
  -- proceed with the evaluation of the `Alt`'s expression. We also make sure
  -- to perform the cvar binding.
  | Evaluate (Case mexpr cvar alts) <- code
  , (Data dcon):args <- unApp mexpr
  , (Alt (DataAlt _ params) expr):_ <- matchDataAlts dcon alts
  , length params == length args =
    let binds = (cvar, mexpr) : zip params args
    in (StkRuleEvalCaseData
       , [state { exec_scope = liftBinds binds scope
                , exec_code = Evaluate expr }])

  -- | Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | Evaluate (Case (Lit lit) cvar alts) <- code
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
    let binds = [(cvar, Lit lit)]
    in (StkRuleEvalCaseLit
       , [state { exec_scope = liftBinds binds scope
                , exec_code = Evaluate expr }])

  -- | We are not able to match any of the stuff, and hit a DEFAULT instead? If
  -- so, we just perform the cvar binding and proceed with the alt expression.
  | Evaluate (Case mexpr cvar alts) <- code
  , (Alt _ expr):_ <- defaultAlts alts =
    let binds = [(cvar, mexpr)]
    in ( StkRuleEvalCaseDefault
       , [state { exec_scope = liftBinds binds scope
                , exec_code = Evaluate expr }])

  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `Scope`. However this is
  -- only done when the matching expression is NOT in value form. Value forms
  -- should be handled by other StkRuleEvalCase* rules.
  | Evaluate (Case mexpr cvar alts) <- code
  , not (isValueForm mexpr scope) =
    let frame = CaseFrame cvar alts scope
    in (StkRuleEvalCaseNonVal
       , [state { exec_stack = pushStack frame stack
                , exec_code = Evaluate mexpr }])

  -- Return forms the `Code`.

  -- We are returning something and the first thing that we have on the stack
  -- is an `UpdateFrame`, this means that we add a redirection pointer to the
  -- `Scope`, and continue with execution. This is the equivalent of performing
  -- memoization on values that we have seen.
  | Just (UpdateFrame frm_name, stack') <- popStack stack
  , Return (Var (Id name ty)) <- code =
  ( StkRuleReturnUpdateVar
  , [state { exec_stack = stack'
           , exec_scope = insertRedirect (frm_name, name) scope
           , exec_code = Return (Var (Id name ty)) }])

  -- If the variable we are returning does not have a `Var` in it at the
  -- immediate top level, then we have to insert it into the `Scope` directly.
  | Just (UpdateFrame frm_name, stack') <- popStack stack
  , Return expr <- code =
  ( StkRuleReturnUpdateNonVar
  , [state { exec_stack = stack'
           , exec_scope = insertEnvObj (frm_name, ExprObj expr) scope
           , exec_code = Return expr }])

  -- In the event that we are returning and we have a `CaseFrame` waiting for
  -- us at the top of the stack, we would simply inject it into the case
  -- expression. We do a lot of assumptions here about the form of expressions!
  | Just (CaseFrame cvar alts frm_scope, stack') <- popStack stack
  , Return expr <- code =
  ( StkRuleReturnCase
  , [state { exec_stack = stack'
           , exec_scope = frm_scope
           , exec_code = Evaluate (Case expr cvar alts) }])

  -- When we have an `ApplyFrame` on the top of the stack, things might get a
  -- bit tricky, since we need to make sure that the thing we end up returning
  -- is appropriately a value. In the case of `Lam`, we need to perform
  -- application, and then go into the expression body.
  | Just (ApplyFrame aexpr, stack') <- popStack stack
  , Return (Lam b lexpr) <- code =
  let binds = [(b, aexpr)]
  in ( StkRuleReturnApplyLam
     , [state { exec_stack = stack'
              , exec_scope = liftBinds binds scope
              , exec_code = Evaluate lexpr }])

  -- When we have an `DataCon` application chain, we need to tack on the
  -- expression in the `ApplyFrame` at the end.
  | Just (ApplyFrame aexpr, stack') <- popStack stack
  , Return dexpr <- code
  , (Data _):xs <- unApp dexpr =
  ( StkRuleReturnApplyData
  , [state { exec_stack = stack'
           , exec_scope = scope
           , exec_code = Return (App dexpr aexpr) }])

  -- When we have an symbolic variable pointer, the best we can do is make
  -- another variable and insert it into the `Scope`. This is the last
  -- condition that we can reasonably handle without creating excessively long
  -- `App` spines, which is only okay for `Data` expressions.
  | Just (ApplyFrame aexpr, stack') <- popStack stack
  , Return (Var (Id name ty)) <- code
  , Just (SymObj (Symbol sid _)) <- lookupScope name scope =
  let (sname, confs') = freshSeededName (idName sid) confs
      sres = Id sname (TyApp (typeOf sid) (typeOf aexpr))
      sym_app = Symbol sres (Just (App (Var sid) aexpr, scope))
  in ( StkRuleReturnApplySym
     , [state { exec_stack = stack'
              , exec_scope = insertEnvObj (sname, SymObj sym_app) scope
              , exec_code = Return (Var sres)
              , exec_names = confs' }])

  | otherwise = (StkError, [])

