module G2.Internals.Interface where

import G2.Internals.Core
import G2.Internals.Preprocessing
import G2.Internals.SMT
import G2.Internals.Symbolic

import G2.Lib.Printers

run :: SMTConverter ast out io -> io -> State -> IO [([Expr], Expr)]
run con hhp state = do
    let preproc_state = runPreprocessing state

    putStrLn $ mkStateStr preproc_state

    let ((lives, states), n) = runN ([preproc_state], []) 200

    putStrLn ("\nNumber of execution states: " ++ (show (length states)))
    {-
    putStrLn $ show lives

    putStrLn " ------------------------- "

    putStrLn $ show n
    -}

    satModelOutputs con hhp states
