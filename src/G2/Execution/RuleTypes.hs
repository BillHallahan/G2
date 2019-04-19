{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Execution.RuleTypes where

import Data.Data (Data, Typeable)

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

data Rule = RuleEvalVal
          | RuleEvalVarNonVal Name
          | RuleEvalVarVal Name
          | RuleEvalUnInt
          | RuleEvalApp Expr

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

          | RuleReturnAppSWHNF

          | RuleReturnECase

          | RuleReturnCast

          | RuleReturnEApplyLamExpr [Name]
          | RuleReturnEApplyLamType [Name]
          | RuleReturnEApplyData
          | RuleReturnEApplySym

          | RuleReturnCAssume
          | RuleReturnCAssert

          | RuleIdentity
          | RulePrimError

          | RuleAnnotation

          | RuleReturnAppSymbFunc
          | RuleReturnReplaceSymbFunc

          | RuleNonDet
          | RuleSymGen

          | RuleReturnCurrExprFr

          | RuleError

          | RuleBind

          | RuleReturn

          | RuleTick
          
          | RuleOther
           deriving (Show, Eq, Read, Typeable, Data)

instance AST e => ASTContainer Rule e where
    containedASTs _ = []
    modifyContainedASTs _ r = r

instance Named Rule where
     names _ = []
     rename _ _ = id
