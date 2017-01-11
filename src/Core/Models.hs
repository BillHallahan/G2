module G2.Core.Models where

import G2.Core.Language

type State = (EEnv, Expr, PC)

type PC = [Pair]

type Pair = (Expr, Alt)

