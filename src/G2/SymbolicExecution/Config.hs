module G2.SymbolicExecution.Config where

import G2.Core.Language
import G2.SymbolicExecution.Engine

lamBindings :: EEnv -> name -> [(Name, Type)] -> (Expr, SymLinkTable)
lamBindings = undefined

initState :: TEnv -> EEnv -> Name -> state
initState = undefined

initStateWithPost :: TEnv -> EEnv -> Name -> Name -> State
initStateWithPost = undefined

runN :: [State] -> Int -> ([State], Int)
runN = undefined

histN :: [State] -> Int -> ([State], Int)
histN = undefined

stackN :: State -> Int -> [State]
stackN = undefined

