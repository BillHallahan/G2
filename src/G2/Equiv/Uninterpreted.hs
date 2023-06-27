module G2.Equiv.Uninterpreted where 

import G2.Language
import qualified G2.Language.ExprEnv as E
import Data.Foldable

-- | Find variables that don't have binding and adjust the epxression environment to treat them as symbolic 
addFreeVarsAsSymbolic :: ExprEnv -> ExprEnv 
addFreeVarsAsSymbolic eenv = let xs = freeVars eenv eenv 
                             in foldl' (flip E.insertSymbolic) eenv xs 


