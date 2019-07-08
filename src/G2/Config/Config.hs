module G2.Config.Config ( Mode (..)
                        , Sharing (..)
                        , SMTSolver (..)
                        , HigherOrderSolver (..)
                        , IncludePath
                        , Config (..)
                        , BoolDef (..)
                        , mkConfig
                        , strArg
                        , boolArg) where


import Data.Char
import Data.List
import qualified Data.Map as M

import System.Directory

data Mode = Regular | Liquid deriving (Eq, Show, Read)

-- | Do we use sharing to only reduce variables once?
data Sharing = Sharing | NoSharing deriving (Eq, Show, Read)

data SMTSolver = ConZ3 | ConCVC4 deriving (Eq, Show, Read)

data HigherOrderSolver = AllFuncs
                       | SingleFunc deriving (Eq, Show, Read)

type IncludePath = FilePath

data Config = Config {
      mode :: Mode
    , baseInclude :: [IncludePath]
    , base :: [FilePath] -- ^ Filepath(s) to base libraries.  Get compiled in order from left to right
    , extraDefaultInclude :: [IncludePath]
    , extraDefaultMods :: [FilePath]
    , logStates :: Maybe String -- ^ If Just, dumps all thes states into the given folder
    , sharing :: Sharing
    , maxOutputs :: Maybe Int -- ^ Maximum number of examples/counterexamples to output.  TODO: Currently works only with LiquidHaskell
    , printCurrExpr :: Bool -- ^ Controls whether the curr expr is printed
    , printExprEnv :: Bool -- ^ Controls whether the expr env is printed
    , printRelExprEnv :: Bool -- ^ Controls whether the portion of the expr env relevant to the curr expr and path constraints is printed
    , printPathCons :: Bool -- ^ Controls whether path constraints are printed
    , returnsTrue :: Bool -- ^ If True, shows only those inputs that do not return True
    , higherOrderSolver :: HigherOrderSolver -- ^ How to try and solve higher order functions
    , smt :: SMTSolver -- ^ Sets the SMT solver to solve constraints with
    , steps :: Int -- ^ How many steps to take when running States
    , cut_off :: Int -- ^ How many steps to take after finding an equally good equiv state, in LH mode
    , switch_after :: Int --- ^ How many steps to take in a single step, in LH mode
    , strict :: Bool -- ^ Should the function output be strictly evaluated?
    , timeLimit :: Int -- ^ Seconds
    , validate :: Bool -- ^ If True, HPC is run on G2's output, to measure code coverage.  TODO: Currently doesn't work
    -- , baseLibs :: [BaseLib]
}

-- mkConfigDef :: Config
-- mkConfigDef = mkConfig [] M.empty

baseRoot :: IO FilePath
baseRoot = do
  g2Dir <- getHomeDirectory >>= \f -> return $ f ++ "/.g2"
  return $ g2Dir ++ "/base-4.9.1.0"


mkConfig :: String -> [String] -> M.Map String [String] -> Config
mkConfig homedir as m = Config {
      mode = Regular
    , baseInclude = baseIncludeDef (strArg "base" as m id homedir)
    , base = baseDef (strArg "base" as m id homedir)
    , extraDefaultInclude = extraDefaultIncludePaths (strArg "extra-base-inc" as m id homedir)
    , extraDefaultMods = extraDefaultPaths (strArg "extra-base" as m id homedir)
    , logStates = strArg "log-states" as m Just Nothing
    , sharing = boolArg' "sharing" as m Sharing Sharing NoSharing
    , maxOutputs = strArg "max-outputs" as m (Just . read) Nothing
    , printCurrExpr = boolArg "print-ce" as m Off
    , printExprEnv = boolArg "print-eenv" as m Off
    , printPathCons = boolArg "print-pc" as m Off
    , printRelExprEnv = boolArg "print-rel-eenv" as m Off
    , returnsTrue = boolArg "returns-true" as m Off
    , higherOrderSolver = strArg "higher-order" as m higherOrderSolArg SingleFunc
    , smt = strArg "smt" as m smtSolverArg ConZ3
    , steps = strArg "n" as m read 1000
    , cut_off = strArg "cut-off" as m read 600
    , switch_after = strArg "switch-after" as m read 300
    , strict = boolArg "strict" as m On
    , timeLimit = strArg "time" as m read 300
    , validate  = boolArg "validate" as m Off
    -- , baseLibs = [BasePrelude, BaseException]
}

baseIncludeDef :: FilePath -> [FilePath]
baseIncludeDef root =
    [ root ++ "/.g2/base-4.9.1.0/Control/Exception/"
    , root ++  "/.g2/base-4.9.1.0/"
    , root ++ "/.g2/base-4.9.1.0/"
    , root ++ "/.g2/base-4.9.1.0/Data/Internal/"
    ]

baseDef :: FilePath -> [FilePath]
baseDef root =
    [ root ++ "/.g2/base-4.9.1.0/Control/Exception/Base.hs"
    , root ++ "/.g2/base-4.9.1.0/Prelude.hs"
    , root ++ "/.g2/base-4.9.1.0/Control/Monad.hs"
    , root ++ "/.g2/base-4.9.1.0/Data/Internal/Map.hs"
    ]

extraDefaultIncludePaths :: FilePath -> [FilePath]
extraDefaultIncludePaths root =
    [ root ++ "/.g2/G2Stubs/src/" ] 

extraDefaultPaths :: FilePath -> [FilePath]
extraDefaultPaths root =
    [ root ++ "/.g2/G2Stubs/src/G2/QuasiQuotes/G2Rep.hs" ] 

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

boolArg' :: String -> [String] -> M.Map String [String] -> b -> b -> b -> b
boolArg' s a m b_default b1 b2 =
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
