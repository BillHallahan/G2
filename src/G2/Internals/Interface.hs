module G2.Internals.Interface where

import G2.Internals.Language
import G2.Internals.Execution
import G2.Internals.Preprocessing
import G2.Internals.SMT


-- | Initialize State with Assume / Assert Conditions
initState :: [Name] -> [Binds] -> Maybe String -> Maybe String -> String -> State
initState tycons binds m_assume m_assert entry = undefined

run = undefined

{-
run :: SMTConverter ast out io -> io -> Int -> State -> IO [([Expr], Expr)]
run con hhp n state = do
    let preproc_state = runPreprocessing state

    let states = runNDepth [preproc_state] n

    putStrLn ("\nNumber of execution states: " ++ (show (length states)))


    satModelOutputs con hhp states
-}
