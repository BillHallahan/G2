-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Stack.Rules
  ( stackReduce
  ) where

import G2.Internals.Language

import G2.Internals.Execution.Support

data StackRule = StkRuleVar
               | StkRuleApp
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
{-
isValueForm :: Expr -> ExprEnv -> Bool
isValueForm (Var var) eenv = vlookupExprEnv var eenv == Nothing
isValueForm (App _ _) _ = False
isValueForm (Let _ _) _ = False
isValueForm (Case _ _ _) _ = False
isValueForm _ _ = True
-}

stackReduce :: ExecState -> Maybe (StackRule, [ExecState])
stackReduce = undefined

-- Hi Bill. Directly translating these from SSTG was harder than I thought. In
-- particular this is because less explicit data structures and forms such as
-- Return and Evaluate are used as well as explicit demarcation of pointers and
-- values. However, I believe in the power of sketchy techniques :)


{-
  -- | Variable lookup.
  | Var var <- curr
  , Just expr <- vlookupExpr var eenv =
    let frame = UpdateFrame (idName var)
    in Just (StkRuleVar
            ,[state { stack = pushStack frame stack
                    , curr_expr = expr }])

  -- | Expression application.
  | App fexpr aexpr <- curr =
    let frame = ApplyFrame aexpr eenv
    in Just (StkRuleApp
            ,[state { stack = pushStack frame stack
                    , curr_expr = fexpr }])

  -- | Let evaluation. I guess if everything is kept in a global scope, there
  -- is not a strong need to differentiate recursive let bindings and whatever.
  -- However, assuming that local scoping is somehow needed to differentiate
  -- things, then this could potentially be useful. Ultimately though, we are
  -- under the assumption that name uniqueness allows us to avoid scoping
  -- problems EXCEPT in cases in which the environment may introduce "cross
  -- contamination" that is the result over overwriting existing values. This
  -- would occur most notably in recursive functions.
  
-}

