module G2.Internals.Config.Config where

import Data.Char
import Data.List

data SMTSolver = Z3 | CVC4

data Config = Config {
      logStates :: Maybe String -- If Just, dumps all thes states into the given folder
    , smt :: SMTSolver
    , smtADTs :: Bool -- If True, uses the SMT solver to solve ADT constraints, else uses a more efficient algorithm
    , steps :: Int -- How many steps to take when running States
}

mkConfigDef :: Config
mkConfigDef = mkConfig []

mkConfig :: [String] -> Config
mkConfig as = Config {
      logStates = mArg "--log-states" as Just Nothing
    , smt = mArg "--smt" as smtSolverArg Z3
    , smtADTs = bArg "--smt-adts" as False
    , steps = mArg "--n" as read 500
}

smtSolverArg :: String -> SMTSolver
smtSolverArg = smtSolverArg' . map toLower

smtSolverArg' :: String -> SMTSolver
smtSolverArg' "z3" = Z3
smtSolverArg' "cvc4" = CVC4
smtSolverArg' _ = error "Unrecognized SMT solver."

-- If the given string is on the command line, inverts the given boolean
bArg :: String -> [String] -> Bool -> Bool
bArg s a b = if s `elem` a then not b else b

mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s a f d = case elemIndex s a of
               Nothing -> d
               Just i -> if i >= length a
                              then error ("Invalid use of " ++ s)
                              else f (a !! (i + 1))

