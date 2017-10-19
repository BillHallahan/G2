{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Execution.RuleTypes where

import G2.Internals.Language.AST

data Rule = RuleEvalVal
          | RuleEvalVarNonVal | RuleEvalVarVal
          | RuleEvalUnInt
          | RuleEvalApp
          | RuleEvalPrimAlreadyNorm
          | RuleEvalPrimToNorm
          | RuleEvalLet
          | RuleEvalCaseData | RuleEvalCaseLit | RuleEvalCaseDefault
                             | RuleEvalCaseSym | RuleEvalCasePrim
                             | RuleEvalCaseNonVal
          | RuleEvalAssume | RuleEvalAssert

          | RuleReturnEUpdateVar | RuleReturnEUpdateNonVar
          | RuleReturnECase
          | RuleReturnEApplyLam | RuleReturnEApplyData
                                | RuleReturnEApplySym

          | RuleReturnCAssume | RuleReturnCAssert

          | RuleIdentity

          | RuleError
           deriving (Show, Eq, Read)

instance AST e => ASTContainer Rule e where
    containedASTs _ = []
    modifyContainedASTs _ r = r
