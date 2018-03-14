module G2.Internals.Config.Config where

import Data.Char
import Data.List
import qualified Data.Map as M

data SMTSolver = Z3 | CVC4

data Config = Config {
      base :: [FilePath] -- Filepath(s) to base libraries.  Get compiled in order from left to right
    , logStates :: Maybe String -- If Just, dumps all thes states into the given folder
    , smt :: SMTSolver -- Sets the SMT solver to solve constraints with
    , smtADTs :: Bool -- If True, uses the SMT solver to solve ADT constraints, else uses a more efficient algorithm
    , steps :: Int -- How many steps to take when running States
    , timeLimit :: Int -- Seconds
}

mkConfigDef :: Config
mkConfigDef = mkConfig [] M.empty

mkConfig :: [String] -> M.Map String [String] -> Config
mkConfig as m = Config {
      base = strArgs "base" as m id ["../base-4.9.1.0/Control/Exception/Base.hs", "../base-4.9.1.0/Prelude.hs"]
    , logStates = strArg "log-states" as m Just Nothing
    , smt = strArg "smt" as m smtSolverArg Z3
    , smtADTs = boolArg "smt-adts" as m False
    , steps = strArg "n" as m read 500
    , timeLimit = strArg "time" as m read 300
}

smtSolverArg :: String -> SMTSolver
smtSolverArg = smtSolverArg' . map toLower

smtSolverArg' :: String -> SMTSolver
smtSolverArg' "z3" = Z3
smtSolverArg' "cvc4" = CVC4
smtSolverArg' _ = error "Unrecognized SMT solver."

-- If the given string is on the command line, inverts the given boolean
-- If --no-[str] is on the command line, sets the option to the given boolean
-- otherwise, looks in the config file, and if there is not option there,
-- looks at the default
boolArg :: String -> [String] -> M.Map String [String] -> Bool -> Bool
boolArg s a m b =
    if "--" ++ s `elem` a 
        then not b 
        else if "--no-" ++ s `elem` a 
            then b
            else case  M.lookup s m of
                Just st -> strToBool st b 
                Nothing -> b

strToBool :: [String] -> Bool -> Bool
strToBool [s] b
    | s' == "true" = True
    | s' == "1" = True
    | s' == "false" = False
    | s' == "0" = False
    | otherwise = b
    where
        s' = map toLower s
strToBool _ b = b

--Converts strings arguments to arbitrary types
strArg :: String -> [String] -> M.Map String [String] -> (String -> a) -> a -> a
strArg s a m f d = 
    case elemIndex ("--" ++ s) a of
        Just i -> if i >= length a
                      then error ("Invalid use of " ++ s)
                      else f (a !! (i + 1))
        Nothing -> case M.lookup s m of 
                      Just st -> strToArg st f d
                      Nothing -> d

strToArg :: [String] -> (String -> a) -> a -> a
strToArg [s] f _ = f s
strToArg _ _ d = d

strArgs :: String -> [String] -> M.Map String [String] -> (String -> a) -> [a] -> [a]
strArgs s a m f d = 
    case elemIndex ("--" ++ s) a of
        Just i -> if i >= length a
                      then error ("Invalid use of " ++ s)
                      else [f (a !! (i + 1))]
        Nothing -> case M.lookup s m of 
                      Just st -> strsToArgs st f
                      Nothing -> d

strsToArgs :: [String] -> (String -> a) -> [a]
strsToArgs =  flip map
