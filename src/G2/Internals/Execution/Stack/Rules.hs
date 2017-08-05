-- | Reduction Rules for Stack Execution Semantics
module G2.Internals.Execution.Stack.Rules
  ( stackReduce
  ) where

import G2.Internals.Language

data StackRule = StkRule deriving (Show, Eq, Read)

stackReduce :: State -> Maybe (StackRule, [State])
stackReduce = undefined

