-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Stack.Rules
  ( stackReduce
  ) where

import G2.Internals.Language

import G2.Internals.Execution.Support

data StackRule = StkRuleVal
               | StkRuleVar | StkRuleUnInt
               | StkRuleApp
               | StkRuleLet
               | StkRuleCase
               deriving (Show, Eq, Read)

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
isValueForm (App _ _) _ = False
isValueForm (Let _ _) _ = False
isValueForm (Case _ _ _) _ = False
isValueForm _ _ = True

bindsToEnvObjList :: Binds -> [(Name, EnvObj)]
bindsToEnvObjList (Binds _ kvs) = map (\(k, v) -> (idName k, ExprObj v)) kvs

liftBinds :: Binds -> Scope -> Scope
liftBinds (Binds _ kvs) scope = insertEnvObjList eobjs scope
  where
    eobjs = map (\(k, v) -> (idName k, ExprObj v)) kvs

stackReduce :: ExecState -> Maybe (StackRule, [ExecState])
stackReduce state @ ExecState { exec_stack = stack
                              , exec_scope = scope
                              , exec_code = code
                              , exec_names = confs
                              , exec_paths = paths }


-- The semantics differ a bit from SSTG a bit, namely in what is and is not
-- returned from the heap. In SSTG, you return either literals or pointers.
-- The distinction is less clear here. For now :)

-- Evaluation form expressions.

  -- | Value form returning.
  | Evaluate expr <- code
  , isValueForm expr scope =
    Just (StkRuleVal
         ,[state { exec_code = Return expr }])

  -- | Downcasting expression from the environment.
  | Evaluate (Var var) <- code
  , Just (ExprObj expr) <- vlookupScope var scope =
    let frame = UpdateFrame (idName var)
    in Just (StkRuleVar
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate expr }])

  -- | Uninterpreted variable lifting.
  | Evaluate (Var var) <- code
  , Nothing <- vlookupScope var scope =
    let sname = freshSeededName (idName var) confs
        svar = Id sname (idType var)
        sym = Symbol svar Nothing
    in Just (StkRuleUnInt
            ,[state { exec_scope = insertEnvObj (idName var, SymObj sym) scope
                    , exec_code = Evaluate (Var var) }])

  -- Push application RHS onto the stack.
  | Evaluate (App fexpr aexpr) <- code =
    let frame = ApplyFrame aexpr scope
    in Just (StkRuleApp
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate fexpr }])

  -- Bind let stuff into the environment.
  | Evaluate (Let binds expr) <- code =
    Just (StkRuleLet
         ,[state { exec_scope = liftBinds binds scope
                 , exec_code = Evaluate expr }])

  -- Do case stuff magic shove the staccccck
  | Evaluate (Case mexpr cvar alts) <- code =
    let frame = CaseFrame cvar alts scope
    in Just (StkRuleCase
            ,[state { exec_stack = pushStack frame stack
                    , exec_code = Evaluate mexpr }])

-- Return form expressions.
  


