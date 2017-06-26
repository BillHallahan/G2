module G2.Internals.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing
import G2.Internals.SMT
import G2.Internals.Symbolic

run :: SMTConverter ast out io -> io -> State -> IO [([Expr], Expr)]
run con hhp state = do
    let preproc_state = runPreprocessing state
    let (states, n) = runN [preproc_state] 250

    -- putStrLn ("Number of execution states: " ++ (show (length states)))

    satModelOutputs con hhp states