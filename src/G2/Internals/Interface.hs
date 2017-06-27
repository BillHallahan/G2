module G2.Internals.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing
import G2.Internals.SMT
import G2.Internals.Symbolic

run :: SMTConverter ast out io -> io -> State -> IO [([Expr], Expr)]
run con hhp state = do
    let preproc_state = runPreprocessing state
    let ((lives, states), n) = runN ([preproc_state], []) 250

    -- putStrLn ("Number of execution states: " ++ (show (length states)))
    {-
    putStrLn $ show lives

    putStrLn " ------------------------- "

    putStrLn $ show preproc_state

    putStrLn $ show n
    -}

    satModelOutputs con hhp states
