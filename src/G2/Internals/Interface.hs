module G2.Internals.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing
import G2.Internals.SMT
import G2.Internals.Symbolic

run :: SMTConverter ast out io -> io -> Int -> State -> IO [([Expr], Expr, out)]
run con hhp n state = do
    let preproc_state = runPreprocessing state

    let states = runNDepth [preproc_state] n

    -- putStrLn ("\nNumber of execution states: " ++ (show (length states)))

    satModelOutputs con hhp states

