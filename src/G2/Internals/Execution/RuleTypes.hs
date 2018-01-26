{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Internals.Execution.RuleTypes where

import G2.Internals.Language

data Rule = RuleEvalVal
          | RuleEvalVarNonVal Name
          | RuleEvalVarVal
          | RuleEvalUnInt
          | RuleEvalApp

          | RuleEvalPrimAlreadyNorm
          | RuleEvalPrimToNorm

          | RuleEvalLet

          | RuleEvalCaseData
          | RuleEvalCaseLit
          | RuleEvalCaseDefault
          | RuleEvalCaseSym
          | RuleEvalCasePrim
          | RuleEvalCaseNonVal

          | RuleEvalCastSplit
          | RuleEvalCast

          | RuleEvalAssume
          | RuleEvalAssert

          | RuleReturnEUpdateVar
          | RuleReturnEUpdateNonVar

          | RuleReturnECase

          | RuleReturnCast

          | RuleReturnEApplyLamExpr
          | RuleReturnEApplyLamType 
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