-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Stack.Rules
  ( stackReduce
  ) where

import G2.Internals.Language

import G2.Internals.Execution.Support

data StackRule = StkEvalRuleVal
               | StkEvalRuleVar | StkEvalRuleUnInt
               | StkEvalRuleApp
               | StkEvalRuleLet
               | StkEvalRuleCaseData | StkEvalRuleCaseLit
                                     | StkEvalRuleCaseOther
                                     | StkEvalRuleCaseDefault
               | StkEvalRuleCaseNonVal
               deriving (Show, Eq, Read)

-- | Unravels the application spine.
unApp :: Expr -> [Expr]
unApp (App f a) = unApp f ++ [a]
unApp expr = [expr]

isDataCon :: Expr -> Bool
isDataCon (Data _) = True
isDataCon _ = False

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
  (x:_) -> isDataCon x
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
stackReduce :: ExecState -> Maybe (StackRule, [ExecState])
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
    Just (StkEvalRuleVal
         ,[state { exec_code = Return expr }])

  -- If our variable points to something on the heap, we first push the current
  -- name of the variable onto the stack and evaluate the expression that it
  -- points to. After the latter is done evaluating, we pop the stack to add
  -- a redirection pointer into the heap.
  | Evaluate (Var var) <- code
  , Just (ExprObj expr) <- vlookupScope var scope =
    let frame = UpdateFrame (idName var)
    in Just (StkEvalRuleVar
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate expr }])

  -- If we encounter a vairable that is in scope, we treated it as a symbolic
  -- object and subject it to uninterpreted evaluation later on. This is done
  -- by injecting it into the heap and then evaluating the same expression
  -- again. This is the essense of memoization / single-evaluation in laziness.
  | Evaluate (Var var) <- code
  , Nothing <- vlookupScope var scope =
    let (sname, re) = freshSeededName (idName var) confs
        svar = Id sname (idType var)
        -- Nothing denotes that this is a "base" symbolic value that is not
        -- dependent on any other expressions.
        sym = Symbol svar Nothing
    in Just (StkEvalRuleUnInt
            ,[state { exec_scope = insertEnvObj (idName var, SymObj sym) scope
                    , exec_code = Evaluate (Var var)
                    , exec_names = confs}])

  -- Push application RHS onto the stack. This is essentially the same as the
  -- original STG rules, but we pretend that every function is (appropriately)
  -- single argument. However one problem is that scope sharing has a redundant
  -- representation because long `App` chains will all share the same scope.
  -- However given actual lazy evaluations within Haskell, all the `Scope`s at
  -- each frame would really be stored in a single location on the actuall
  -- Haskell heap during execution.
  | Evaluate (App fexpr aexpr) <- code =
    let frame = ApplyFrame aexpr scope
    in Just (StkEvalRuleApp
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate fexpr }])

  -- Lift all the let bindings into the environment and continue with scope and
  -- continue with evaluation of the let expression.
  | Evaluate (Let binds expr) <- code =
    Just (StkEvalRuleLet
         ,[state { exec_scope = liftBinds binds scope
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
    in Just (StkEvalRuleCaseData
            ,[state { exec_scope = liftBinds binds scope
                    , exec_code = Evaluate expr }])

  -- | Is the current expression able to match with a literal based `Alt`? If
  -- so, we do the cvar binding, and proceed with evaluation of the body.
  | Evaluate (Case (Lit lit) cvar alts) <- code
  , (Alt (LitAlt _) expr):_ <- matchLitAlts lit alts =
    let binds = [(cvar, Lit lit)]
    in Just (StkEvalRuleCaseLit
            ,[state { exec_scope = liftBinds binds scope
                    , exec_code = Evaluate expr }])

  -- | We are not able to match any of the stuff, and hit a DEFAULT instead? If
  -- so, we just perform the cvar binding and proceed with the alt expression.
  | Evaluate (Case mexpr cvar alts) <- code
  , (Alt _ expr):_ <- defaultAlts alts =
    let binds = [(cvar, mexpr)]
    in Just (StkEvalRuleCaseDefault
            ,[state { exec_scope = liftBinds binds scope
                    , exec_code = Evaluate expr }])

  -- Case evaluation also uses the stack in graph reduction based evaluation
  -- semantics. The case's binding variable and alts are pushed onto the stack
  -- as a `CaseFrame` along with their appropriate `Scope`. However this is
  -- only done when the matching expression is NOT in value form. Value forms
  -- should be handled by other StkEvalRuleCase* rules.
  | Evaluate (Case mexpr cvar alts) <- code
  , not (isValueForm mexpr scope) =
    let frame = CaseFrame cvar alts scope
    in Just (StkEvalRuleCaseNonVal
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate mexpr }])

  -- Return forms the `Code`.


