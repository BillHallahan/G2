module G2.Config.Config ( Mode (..)
                        , LogMode (..)
                        , LogMethod (..)
                        , Sharing (..)
                        , SMTSolver (..)
                        , SearchStrategy (..)
                        , HigherOrderSolver (..)
                        , FpHandling (..)
                        , NonRedPathCons (..)
                        , SMTStrings (..)
                        , IncludePath
                        , Config (..)
                        , BoolDef (..)
                        , InstTV (..)
                        , ShowType (..)
                        , mkConfig
                        , mkConfigDirect

                        , mkLogMode
                        
                        , strArg
                        , boolArg
                        , boolArg'

                        , baseDef
                        , baseSimple) where


import Data.Char
import Data.List as L
import qualified Data.Map as M
import Options.Applicative
import Text.Read


data Mode = Regular | Liquid deriving (Eq, Show, Read)

data LogMode = Log LogMethod String | NoLog deriving (Eq, Show, Read)

data LogMethod = Raw | Pretty deriving (Eq, Show, Read)

-- | Do we use sharing to only reduce variables once?
data Sharing = Sharing | NoSharing deriving (Eq, Show, Read)

-- Instantiate type variables before or after symbolic execution
data InstTV = InstBefore | InstAfter deriving (Eq, Show, Read)

-- Determining whether we want to show more type informations
data ShowType = Lax | Aggressive deriving (Eq, Show, Read)

data SMTSolver = ConZ3 | ConCVC4 deriving (Eq, Show, Read)

data SearchStrategy = Iterative | Subpath deriving (Eq, Show, Read)

data HigherOrderSolver = AllFuncs
                       | SingleFunc
                       | SymbolicFunc deriving (Eq, Show, Read)

data FpHandling = RealFP | RationalFP deriving (Eq, Show, Read)

data NonRedPathCons = Nrpc | NoNrpc deriving (Eq, Show, Read)

data SMTStrings = UseSMTStrings | NoSMTStrings deriving (Eq, Show, Read)

type IncludePath = FilePath

data Config = Config {
      mode :: Mode
    , baseInclude :: [IncludePath]
    , base :: [FilePath] -- ^ Filepath(s) to base libraries.  Get compiled in order from left to right
    , extraDefaultInclude :: [IncludePath]
    , extraDefaultMods :: [FilePath]
    , includePaths :: Maybe [FilePath] -- ^ Paths to search for modules
    , print_output :: Bool -- ^ Print function outputs
    , logStates :: LogMode -- ^ Determines whether to Log states, and if logging states, how to do so.
    , logEveryN :: Int -- ^ If logging states, log every nth state
    , logAfterN :: Int -- ^ Logs state only after the nth state
    , logConcPCGuide :: Maybe String -- ^ Log states only if they match the ConcPCGuide in the provided file
    , logPath :: [Int] -- ^ Log states that are following on or proceed from some path, passed as a list i.e. [1, 2, 1]
    , sharing :: Sharing
    , instTV :: InstTV -- allow the instantiation of types in the beginning or it's instantiate symbolically by functions
    , showType :: ShowType -- allow user to see more type information when they are logging states for the execution
    , maxOutputs :: Maybe Int -- ^ Maximum number of examples/counterexamples to output.  TODO: Currently works only with LiquidHaskell
    , returnsTrue :: Bool -- ^ If True, shows only those inputs that do not return True
    , check_asserts :: Bool -- ^ If True, shows only those inputs that violate asserts
    , error_asserts :: Bool -- ^ If True, treat error as an assertion violation
    , higherOrderSolver :: HigherOrderSolver -- ^ How to try and solve higher order functions
    , search_strat :: SearchStrategy -- ^ The search strategy for the symbolic executor to use
    , subpath_length :: Int -- ^ When using subpath search strategy, the length of the subpaths.
    , fp_handling :: FpHandling -- ^ Whether to use real floating point values or rationals
    , smt :: SMTSolver -- ^ Sets the SMT solver to solve constraints with
    , smt_strings :: SMTStrings -- ^ Sets whether the SMT solver should be used to solve string constraints
    , step_limit :: Bool -- ^ Should steps be limited when running states?
    , steps :: Int -- ^ How many steps to take when running States
    , time_solving :: Bool -- ^ Output the amount of time spent checking/solving path constraints
    , print_num_solver_calls :: Bool -- ^ Output the number of calls made to check/solve path constraints
    , print_smt :: Bool -- ^ Output SMT formulas when checking/solving path constraints
    , accept_times :: Bool -- ^ Output the time each state is accepted
    , states_at_time :: Bool -- ^ Output time and number of states each time a state is added/removed
    , states_at_step :: Bool -- ^ Output step and number of states at each step where a state is added/removed
    , print_num_red_rules :: Bool -- ^ Output the total number of reduction rules
    , print_num_red_rules_per_state :: Bool  -- ^ Output the number of reduction rules per accepted state
    , print_nrpcs :: Bool -- ^ Output generated NRPCs
    , approx_discard :: Bool -- ^ Discard states that are approximated by other states
    , hpc :: Bool -- ^ Should HPC ticks be generated and tracked during execution?
    , hpc_discard_strat :: Bool -- ^ Discard states that cannot reach any new HPC ticks
    , hpc_print_times :: Bool -- ^ Print the time each HPC tick is reached?
    , hpc_print_ticks :: Bool -- ^ Print each HPC tick number that was reached?
    , strict :: Bool -- ^ Should the function output be strictly evaluated?
    , timeLimit :: Int -- ^ Seconds
    , validate :: Bool -- ^ If True, run on G2's input, and check against expected output.
    , measure_coverage :: Bool -- ^ Use HPC to measure code coverage
    , lib_nrpc :: NonRedPathCons -- ^ Whether to use NRPCs for library functions or not
    , approx_nrpc :: NonRedPathCons -- ^ Use approximation and NRPCs to avoid repeated exploration of equivalent function calls
    , symbolic_func_nrpc :: NonRedPathCons -- ^ Whether to use NRPCs for symbolic functions or not
    , print_num_nrpc :: Bool -- ^ Output the number of NRPCs for each accepted state
    , print_num_post_call_func_arg :: Bool -- ^ Output the number of post call and function argument states
}

mkConfig :: String -> Parser Config
mkConfig homedir = Config Regular
    <$> mkBaseInclude homedir
    <*> mkBase homedir
    <*> mkExtraDefault homedir
    <*> pure []
    <*> mkIncludePaths
    <*> flag True False (long "no-print-outputs" <> help "Print function outputs")
    <*> mkLogMode
    <*> option auto (long "log-every-n"
                   <> metavar "LN"
                   <> value 0
                   <> help "if logging states, log every nth state")
    <*> option auto (long "log-after-n"
                   <> metavar "LA"
                   <> value 0
                   <> help "logs state only after the nth state")
    <*> option (maybeReader (Just . Just))
                 (long "log-conc-pc"
                   <> metavar "LCPC"
                   <> value Nothing
                   <> help "logs state only if they match the concretizations and path constraints specified in the provided file")
    <*> option auto (long "log-path"
                   <> metavar "LP"
                   <> value []
                   <> help "log states that are following on or proceed from some path, passed as a list i.e. [1, 2, 1]")
    <*> flag Sharing NoSharing (long "no-sharing" <> help "disable sharing")
    <*> flag InstBefore InstAfter (long "inst-after" <> help "select to instantiate type variables after symbolic execution, rather than before")
    <*> flag Lax Aggressive (long "show-types" <> help "set to show more type information when logging states")
    <*> mkMaxOutputs
    <*> switch (long "returns-true" <> help "assert that the function returns true, show only those outputs which return false")
    <*> switch (long "check-asserts" <> help "show only inputs that violate assertions")
    <*> switch (long "error-asserts" <> help "treat error as an assertion violation")
    <*> mkHigherOrder
    <*> mkSearchStrategy
    <*> option auto (long "subpath-len"
                   <> metavar "L"
                   <> value 4
                   <> help "when using subpath search strategy, the length of the subpaths")
    <*> flag RealFP RationalFP (long "no-real-floats"
                                <> help "Represent floating point values precisely.  When off, overapproximate as rationals.")
    <*> mkSMTSolver
    <*> flag NoSMTStrings UseSMTStrings (long "smt-strings" <> help "Sets whether the SMT solver should be used to solve string constraints")
    <*> flag True False (long "no-step-limit" <> help "disable step limit")
    <*> option auto (long "n"
                   <> metavar "N"
                   <> value 1000
                   <> help "how many steps to take when running states")
    <*> switch (long "solver-time" <> help "output the amount of time spent checking/solving path constraints")
    <*> switch (long "print-num-solver-calls" <> help "output the number of calls made to check/solve path constraints")
    <*> switch (long "print-smt" <> help "output SMT formulas when checking/solving path constraints")
    <*> switch (long "accept-times" <> help "output the time each state is accepted")
    <*> switch (long "states-at-time" <> help "output time and number of states each time a state is added/removed")
    <*> switch (long "states-at-step" <> help "output step and number of states at each step where a state is added/removed")
    <*> switch (long "print-num-red-rules" <> help "output the total number of reduction rules")
    <*> switch (long "print-num-red-rules-per-state" <> help "output the number of reduction rules per accepted state")
    <*> switch (long "print-nrpc" <> help "output generated nrpcs")
    <*> flag False True (long "approx-discard"
                      <> help "Discard states that are approximated by other states")
    <*> flag False True (long "hpc"
                      <> help "Generate and report on HPC ticks")
    <*> flag False True (long "hpc-discard-strat" <> help "Discard states that cannot reach any new HPC ticks")
    <*> switch (long "hpc-print-times" <> help "Print the time each HPC tick is reached?")
    <*> switch (long "hpc-print-ticks" <> help "Print each HPC tick number that was reached?")
    <*> flag True False (long "no-strict" <> help "do not evaluate the output strictly")
    <*> option auto (long "time"
                   <> metavar "T"
                   <> value 600
                   <> help "time limit, in seconds")
    <*> switch (long "validate" <> help "use GHC to automatically compile and run on generated inputs, and check that generated outputs are correct")
    <*> switch (long "measure-coverage" <> help "use HPC to measure code coverage")
    <*> flag NoNrpc Nrpc (long "lib-nrpc" <> help "execute with non reduced path constraints")
    <*> flag NoNrpc Nrpc (long "approx-nrpc" <> help "Use approximation and NRPCs to avoid repeated exploration of equivalent function calls")
    <*> flag NoNrpc Nrpc (long "higher-nrpc" <> help "use NRPCs to delay execution of library functions")
    <*> flag False True (long "print-num-nrpc" <> help "output the number of NRPCs for each accepted state")
    <*> flag False True (long "print-num-higher-states" <> help "output the number of post call and function argument states (from higher order coverage checking)")

mkBaseInclude :: String -> Parser [IncludePath]
mkBaseInclude homedir =
    option (eitherReader (Right . baseIncludeDef))
            ( long "base"
            <> metavar "FILE"
            <> value (baseIncludeDef homedir)
            <> help "where to look for base files")

mkBase :: String -> Parser [IncludePath]
mkBase homedir =
    option (eitherReader (Right . baseDef))
            ( long "base-def"
            <> metavar "FILE"
            <> value (baseDef homedir)
            <> help "where to look for base files")

mkExtraDefault :: String -> Parser [IncludePath]
mkExtraDefault homedir =
    option (eitherReader (\v -> Right (v:extraDefaultIncludePaths homedir)))
            ( long "extra-def"
            <> metavar "FILE"
            <> value (extraDefaultIncludePaths homedir)
            <> help "where to look for base files")

mkIncludePaths :: Parser (Maybe [FilePath])
mkIncludePaths = 
    option (maybeReader (Just . Just . (:[])))
            ( long "include"
            <> metavar "I"
            <> value Nothing
            <> help "paths to search for included modules")

mkLogMode :: Parser LogMode
mkLogMode =
    (option (eitherReader (Right . Log Raw))
            (long "log-states"
            <> metavar "FOLDER"
            <> value NoLog
            <> help "log all states with raw printing"))
    <|>
    (option (eitherReader (Right . Log Pretty))
            (long "log-pretty"
            <> metavar "FOLDER"
            <> value NoLog
            <> help "log all states with pretty printing"))

mkMaxOutputs :: Parser (Maybe Int)
mkMaxOutputs =
    option (maybeReader (Just . readMaybe))
            ( long "max-outputs"
            <> metavar "MAX"
            <> value Nothing
            <> help "the maximum number of input/output pairs to output")

mkHigherOrder :: Parser HigherOrderSolver
mkHigherOrder =
    option (eitherReader (\s -> case s of
                                    "all" -> Right AllFuncs
                                    "single" -> Right SingleFunc
                                    "symbolic" -> Right SymbolicFunc
                                    _ -> Left "Unsupported higher order function handling"))
            ( long "higher-order"
            <> metavar "HANDLING"
            <> value SingleFunc
            <> help "either all or single, to specify whether all possible higher order instantiations should be searched for, or just a single instantiation")

mkSMTSolver :: Parser SMTSolver
mkSMTSolver =
    option (eitherReader (\s -> case s of
                                    "z3" -> Right ConZ3
                                    "cvc4" -> Right ConCVC4
                                    _ -> Left "Unsupported SMT solver"))
            ( long "smt"
            <> metavar "SMT-SOLVER"
            <> value ConZ3
            <> help "either z3 or cvc4, to select the solver to use")

mkSearchStrategy :: Parser SearchStrategy
mkSearchStrategy =
    option (eitherReader (\s -> case s of
                                    "iter" -> Right Iterative
                                    "subpath" -> Right Subpath
                                    _ -> Left "Unsupported search strategy"))
            ( long "search"
            <> metavar "SEARCH"
            <> value Iterative
            <> help "either iter or subpath, to select a search strategy")

mkConfigDirect :: String -> [String] -> M.Map String [String] -> Config
mkConfigDirect homedir as m = Config {
      mode = Regular
    , baseInclude = baseIncludeDef (strArg "base" as m id homedir)
    , base = baseDef (strArg "base" as m id homedir)
    , extraDefaultInclude = extraDefaultIncludePaths (strArg "extra-base-inc" as m id homedir)
    , extraDefaultMods = []
    , includePaths = Nothing
    , print_output = True
    , logStates = strArg "log-states" as m (Log Raw)
                        (strArg "log-pretty" as m (Log Pretty) NoLog)
    , logEveryN = 0
    , logAfterN = 0
    , logConcPCGuide = Nothing
    , logPath = []
    , sharing = boolArg' "sharing" as Sharing Sharing NoSharing
    , instTV = InstBefore
    , showType = Lax
    , maxOutputs = strArg "max-outputs" as m (Just . read) Nothing
    , returnsTrue = boolArg "returns-true" as m Off
    , check_asserts = boolArg "check-asserts" as m Off
    , error_asserts = boolArg "error-asserts" as m Off
    , higherOrderSolver = strArg "higher-order" as m higherOrderSolArg SingleFunc
    , search_strat = Iterative
    , subpath_length = 4
    , fp_handling = RealFP
    , smt = strArg "smt" as m smtSolverArg ConZ3
    , smt_strings = NoSMTStrings
    , step_limit = boolArg' "no-step-limit" as True True False
    , steps = strArg "n" as m read 1000
    , time_solving = False
    , print_num_solver_calls = False
    , print_smt = False
    , accept_times = boolArg "accept-times" as m Off
    , states_at_time = False
    , states_at_step = False
    , print_num_red_rules = False
    , print_num_red_rules_per_state = False
    , print_nrpcs = False
    , approx_discard = False
    , hpc = False
    , hpc_discard_strat = False
    , hpc_print_times = False
    , hpc_print_ticks = False
    , strict = boolArg "strict" as m On
    , timeLimit = strArg "time" as m read 300
    , validate  = boolArg "validate" as m Off
    , measure_coverage = False
    , lib_nrpc = NoNrpc
    , approx_nrpc = NoNrpc
    , symbolic_func_nrpc = NoNrpc
    , print_num_nrpc = False
    , print_num_post_call_func_arg = False
}

baseIncludeDef :: FilePath -> [FilePath]
baseIncludeDef root =
    [ root ++ "/.g2/base-4.9.1.0/Control/Exception/"
    , root ++ "/.g2/base-4.9.1.0/"
    , root ++ "/.g2/base-4.9.1.0/Data/Internal/"
    ]

baseDef :: FilePath -> [FilePath]
baseDef root = baseSimple root

baseSimple :: FilePath -> [FilePath]
baseSimple root =
    [ root ++ "/.g2/base-4.9.1.0/Control/Exception/Base.hs"
    , root ++ "/.g2/base-4.9.1.0/Prelude.hs"
    , root ++ "/.g2/base-4.9.1.0/Control/Monad.hs" ]

extraDefaultIncludePaths :: FilePath -> [FilePath]
extraDefaultIncludePaths root =
    [ root ++ "/.g2/G2Stubs/src/" ] 

smtSolverArg :: String -> SMTSolver
smtSolverArg = smtSolverArg' . map toLower

smtSolverArg' :: String -> SMTSolver
smtSolverArg' "z3" = ConZ3
smtSolverArg' "cvc4" = ConCVC4
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

boolArg' :: String -> [String] -> b -> b -> b -> b
boolArg' s a b_default b1 b2 =
    if "--" ++ s `elem` a 
        then b1
        else if "--no-" ++ s `elem` a 
            then b2
            else b_default


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
