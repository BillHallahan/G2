{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module G2.Execution.RuleTypes where

import Data.Data (Data, Typeable)

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Hashable
import qualified Data.Sequence as S

import GHC.Generics (Generic)

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
           deriving (Show, Eq, Read, Typeable, Data, Generic)

instance Hashable Rule

instance AST e => ASTContainer Rule e where
    containedASTs _ = []
    modifyContainedASTs _ r = r

instance Named Rule where
     names _ = S.empty
     rename _ _ = id
