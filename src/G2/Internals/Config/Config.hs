module G2.Internals.Config.Config where

import Data.List

data Config = Config {
      logStates :: Maybe String -- If Just, dumps all thes states into the given folder
    , smtADTs :: Bool
    , steps :: Int -- How many steps to take when running States
}

mkConfigDef :: Config
mkConfigDef = mkConfig []

mkConfig :: [String] -> Config
mkConfig as = Config {
      logStates = mArg "--log-states" as Just Nothing
    , smtADTs = bArg "--smt-adts" as False
    , steps = mArg "--n" as read 500
}

-- If the given string is on the command line, inverts the given boolean
bArg :: String -> [String] -> Bool -> Bool
bArg s a b = if s `elem` a then not b else b

mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s a f d = case elemIndex s a of
               Nothing -> d
               Just i -> if i >= length a
                              then error ("Invalid use of " ++ s)
                              else f (a !! (i + 1))