module G2.Internals.Config.Config where

import Data.Char
import Data.List
import qualified Data.Map as M

data Mode = Regular | Liquid deriving (Eq, Show, Read)

data SMTSolver = Z3 | CVC4 deriving (Eq, Show, Read)

data HigherOrderSolver = AllFuncs
                       | SingleFunc deriving (Eq, Show, Read)

data Config = Config {
      mode :: Mode
    , base :: [FilePath] -- ^ Filepath(s) to base libraries.  Get compiled in order from left to right
    , logStates :: Maybe String -- ^ If Just, dumps all thes states into the given folder
    , maxOutputs :: Maybe Int -- ^ Maximum number of examples/counterexamples to output.  TODO: Currently works only with LiquidHaskell
    , printCurrExpr :: Bool -- ^ Controls whether the curr expr is printed
    , printExprEnv :: Bool -- ^ Controls whether the expr env is printed
    , printRelExprEnv :: Bool -- ^ Controls whether the portion of the expr env relevant to the curr expr and path constraints is printed
    , printPathCons :: Bool -- ^ Controls whether path constraints are printed
    , returnsTrue :: Bool -- ^ If True, shows only those inputs that do not return True
    , higherOrderSolver :: HigherOrderSolver -- ^ How to try and solve higher order functions
    , smt :: SMTSolver -- ^ Sets the SMT solver to solve constraints with
    , smtADTs :: Bool -- ^ If True, uses the SMT solver to solve ADT constraints, else uses a more efficient algorithm
    , steps :: Int -- ^ How many steps to take when running States
    , strict :: Bool -- ^ Should the function output be strictly evaluated?
    , timeLimit :: Int -- ^ Seconds
    , validate :: Bool -- ^ If True, HPC is run on G2's output, to measure code coverage.  TODO: Currently doesn't work
}

mkConfigDef :: Config
mkConfigDef = mkConfig [] M.empty

mkConfig :: [String] -> M.Map String [String] -> Config
mkConfig as m = Config {
      mode = Regular
    , base = strArgs "base" as m id ["../base-4.9.1.0/Control/Exception/Base.hs", "../base-4.9.1.0/Prelude.hs"]
    , logStates = strArg "log-states" as m Just Nothing
    , maxOutputs = strArg "max-outputs" as m (Just . read) Nothing
    , printCurrExpr = boolArg "print-ce" as m Off
    , printExprEnv = boolArg "print-eenv" as m Off
    , printPathCons = boolArg "print-pc" as m Off
    , printRelExprEnv = boolArg "print-rel-eenv" as m Off
    , returnsTrue = boolArg "returns-true" as m Off
    , higherOrderSolver = strArg "higher-order" as m higherOrderSolArg SingleFunc
    , smt = strArg "smt" as m smtSolverArg Z3
    , smtADTs = boolArg "smt-adts" as m Off
    , steps = strArg "n" as m read 500
    , strict = boolArg "strict" as m On
    , timeLimit = strArg "time" as m read 300
    , validate  = boolArg "validate" as m Off

}

smtSolverArg :: String -> SMTSolver
smtSolverArg = smtSolverArg' . map toLower

smtSolverArg' :: String -> SMTSolver
smtSolverArg' "z3" = Z3
smtSolverArg' "cvc4" = CVC4
smtSolverArg' _ = error "Unrecognized SMT solver."

higherOrderSolArg :: String -> HigherOrderSolver
higherOrderSolArg = higherOrderSolArg' . map toLower

higherOrderSolArg' :: String -> HigherOrderSolver
higherOrderSolArg' "all" = AllFuncs
higherOrderSolArg' "single" = SingleFunc
higherOrderSolArg' _ = error "Unrecognized higher order solver."

data BoolDef = On | Off deriving (Eq, Show)

-- If the given string is on the command line, returns True
-- If --no-[str] is on the command line, returns False
-- otherwise, looks in the config file, and if there is not option there,
-- uses the default to decide
boolArg :: String -> [String] -> M.Map String [String] -> BoolDef -> Bool
boolArg s a m bd =
    let
        d = if bd == On then True else False
    in
    if "--" ++ s `elem` a 
        then True
        else if "--no-" ++ s `elem` a 
            then False
            else case  M.lookup s m of
                Just st -> strToBool st d
                Nothing -> d

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
