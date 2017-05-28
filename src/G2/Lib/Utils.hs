module G2.Lib.Utils where

-- | Batman delivers only Just-ice.
batman :: Maybe a -> String -> a
batman (Just a) msg = a
batman Nothing msg  = error msg

