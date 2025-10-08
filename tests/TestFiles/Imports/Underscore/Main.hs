module Call where

import Under_under

call :: String -> String
call x = f (f x) ++ "!"