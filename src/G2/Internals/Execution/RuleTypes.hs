{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Execution.RuleTypes where

import G2.Internals.Language

data Rule = RuleEvalVal
          | RuleEvalVarNonVal Name
          | RuleEvalVarVal Name
          | RuleEvalUnInt
          | RuleEvalApp

          | RuleEvalPrimAlreadyNorm
          | RuleEvalPrimToNorm

          | RuleEvalLet [Name]

          | RuleEvalCaseData [Name]
          | RuleEvalCaseLit
          | RuleEvalCaseDefault
          | RuleEvalCaseSym
          | RuleEvalCasePrim
          | RuleEvalCaseNonVal

          | RuleEvalCastSplit
          | RuleEvalCast

          | RuleEvalAssume
          | RuleEvalAssert

          | RuleReturnEUpdateVar Name
          | RuleReturnEUpdateNonVar Name

          | RuleReturnECase

          | RuleReturnCast

          | RuleReturnEApplyLamExpr [Name]
          | RuleReturnEApplyLamType [Name]
          | RuleReturnEApplyData
          | RuleReturnEApplySym

          | RuleReturnCAssume
          | RuleReturnCAssert

          | RuleIdentity

          | RuleError
           deriving (Show, Eq, Read)

instance AST e => ASTContainer Rule e where
    containedASTs _ = []
    modifyContainedASTs _ r = r

instance Named Rule where
     names _ = []
     rename _ _ = id
