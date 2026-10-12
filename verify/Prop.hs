module Main where

import System.Environment
import qualified QuickCheck as QC
import qualified SmallCheck as SC

main :: IO ()
main = do
    ars <- getArgs
    case ars of
        [] -> QC.main
        "qc":as -> withArgs as QC.main
        "sc":as -> withArgs as SC.main
        _ -> error "Unrecognized argument"
