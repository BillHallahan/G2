module G2.Internals.Config.Config where

import Data.List

data Config = Config {
	  logStates :: Maybe String -- If Just, dumps all thes states into the given folder
	, steps :: Int -- How many steps to take when running States
}

mkConfigDef :: Config
mkConfigDef = mkConfig []

mkConfig :: [String] -> Config
mkConfig as = Config {
	  logStates = mArg "--log-states" as Just Nothing
	, steps = mArg "--n" as read 500
}

mArg :: String -> [String] -> (String -> a) -> a -> a
mArg s a f d = case elemIndex s a of
               Nothing -> d
               Just i -> if i >= length a
                              then error ("Invalid use of " ++ s)
                              else f (a !! (i + 1))
