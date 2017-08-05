-- | Reduction Rules for Lambda Execution Semantics
module G2.Internals.Execution.Lambda.Rules
    ( lambdaReduce
    ) where

import G2.Internals.Language

data LambdaRule = LamRule deriving (Show, Eq, Read)

lambdaReduce :: State -> Maybe (LambdaRule, [State])
lambdaReduce = undefined

