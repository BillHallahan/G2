module G2.Internals.Liquid.Types where

import G2.Internals.Language

import Language.Haskell.Liquid.Types
import Language.Haskell.Liquid.Constraint.Types
import Language.Fixpoint.Types.Constraints

data LHOutput = LHOutput { ghcI :: GhcInfo
                         , cgI :: CGInfo
                         , solution :: FixSolution }

type Measures = ExprEnv
