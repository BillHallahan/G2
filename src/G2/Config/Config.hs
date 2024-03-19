module G2.Config.Config ( Mode (..)
                        , LogMode (..)
                        , LogMethod (..)
                        , Sharing (..)
                        , SMTSolver (..)
                        , SearchStrategy (..)
                        , HigherOrderSolver (..)
                        , NonRedPathCons (..)
                        , IncludePath
                        , Config (..)
                        , BoolDef (..)
                        , mkConfig
                        , mkConfigDirect

                        , mkLogMode
                        
                        , strArg
                        , boolArg
                        , boolArg'

                        , baseDef
                        , baseSimple) where


import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Monoid ((<>))
import Options.Applicative
import Text.Read

data Mode = Regular | Liquid deriving (Eq, Show, Read)

data LogMode = Log LogMethod String | NoLog deriving (Eq, Show, Read)

data LogMethod = Raw | Pretty deriving (Eq, Show, Read)

-- | Do we use sharing to only reduce variables once?
data Sharing = Sharing | NoSharing deriving (Eq, Show, Read)

data SMTSolver = ConZ3 | ConCVC4 deriving (Eq, Show, Read)

data SearchStrategy = Iterative | Subpath deriving (Eq, Show, Read)

data HigherOrderSolver = AllFuncs
                       | SingleFunc
                       | SymbolicFunc 
                       | SymbolicFuncTemplate deriving (Eq, Show, Read)

data NonRedPathCons = Nrpc | NoNrpc deriving (Eq, Show, Read)

type IncludePath = FilePath

data Config = Config {
      mode :: Mode
    , baseInclude :: [IncludePath]
    , base :: [FilePath] -- ^ Filepath(s) to base libraries.  Get compiled in order from left to right
    , extraDefaultInclude :: [IncludePath]
    , extraDefaultMods :: [FilePath]
    , logStates :: LogMode -- ^ Determines whether to Log states, and if logging states, how to do so.
    , sharing :: Sharing
    , maxOutputs :: Maybe Int -- ^ Maximum number of examples/counterexamples to output.  TODO: Currently works only with LiquidHaskell
    , returnsTrue :: Bool -- ^ If True, shows only those inputs that do not return True
    , higherOrderSolver :: HigherOrderSolver -- ^ How to try and solve higher order functions
    , search_strat :: SearchStrategy -- ^ The search strategy for the symbolic executor to use
    , subpath_length :: Int -- ^ When using subpath search strategy, the length of the subpaths.
    , smt :: SMTSolver -- ^ Sets the SMT solver to solve constraints with
    , steps :: Int -- ^ How many steps to take when running States
    , hpc :: Bool -- ^ Should HPC ticks be generated and tracked during execution?
    , strict :: Bool -- ^ Should the function output be strictly evaluated?
    , timeLimit :: Int -- ^ Seconds
    , validate :: Bool -- ^ If True, run on G2's input, and check against expected output.
    , nrpc :: NonRedPathCons -- ^ Whether to execute using non reduced path constraints or not
}

mkConfig :: String -> Parser Config
mkConfig homedir = Config Regular
    <$> mkBaseInclude homedir
    <*> mkBase homedir
    <*> mkExtraDefault homedir
    <*> pure []
    <*> mkLogMode
    <*> flag Sharing NoSharing (long "no-sharing" <> help "disable sharing")
    <*> mkMaxOutputs
    <*> switch (long "returns-true" <> help "assert that the function returns true, show only those outputs which return false")
    <*> mkHigherOrder
    <*> mkSearchStrategy
    <*> option auto (long "subpath-len"
                   <> metavar "L"
                   <> value 4
                   <> help "when using subpath search strategy, the length of the subpaths")
    <*> mkSMTSolver
    <*> option auto (long "n"
                   <> metavar "N"
                   <> value 1000
                   <> help "how many steps to take when running states")
    <*> flag False True (long "hpc"
                      <> help "Generate and report on HPC ticks")
    <*> flag True False (long "no-strict" <> help "do not evaluate the output strictly")
    <*> option auto (long "time"
                   <> metavar "T"
                   <> value 600
                   <> help "time limit, in seconds")
    <*> switch (long "validate" <> help "use GHC to automatically compile and run on generated inputs, and check that generated outputs are correct")
    <*> flag Nrpc NoNrpc (long "no-nrpc" <> help "execute without non reduced path constraints")

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
                                    "symbolic-temp" -> Right SymbolicFuncTemplate
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
    , logStates = strArg "log-states" as m (Log Raw)
                        (strArg "log-pretty" as m (Log Pretty) NoLog)
    , sharing = boolArg' "sharing" as Sharing Sharing NoSharing

    , maxOutputs = strArg "max-outputs" as m (Just . read) Nothing
    , returnsTrue = boolArg "returns-true" as m Off
    , higherOrderSolver = strArg "higher-order" as m higherOrderSolArg SingleFunc
    , search_strat = Iterative
    , subpath_length = 4
    , smt = strArg "smt" as m smtSolverArg ConZ3
    , steps = strArg "n" as m read 1000
    , hpc = False
    , strict = boolArg "strict" as m On
    , timeLimit = strArg "time" as m read 300
    , validate  = boolArg "validate" as m Off
    , nrpc = Nrpc
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
