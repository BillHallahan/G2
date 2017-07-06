module G2.Internals.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing
import G2.Internals.SMT
import G2.Internals.Symbolic

import G2.Lib.Printers

run :: SMTConverter ast out io -> io -> Int -> State -> IO [([Expr], Expr)]
run con hhp n state = do
    let preproc_state = runPreprocessing state

    -- putStrLn $ mkStateStr preproc_state

    let ((lives, states), _) = runN ([preproc_state], []) n

    -- putStrLn ("\nNumber of execution states: " ++ (show (length states)))

    satModelOutputs con hhp states
