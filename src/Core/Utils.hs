module G2.Core.Utils where

import G2.Core.Language
import G2.Core.Evaluator

import qualified Data.List as L

mkStateStr :: State -> String
mkStateStr (tv, ev, expr, pc) = L.intercalate "\n" [ts, es, xs, ps]
  where ts = show tv
        es = show ev
        xs = show expr
        ps = show pc

mkStatesStr :: [State] -> String
mkStatesStr []     = ""
mkStatesStr (s:[]) = mkStateStr s
mkStatesStr (s:ss) = mkStateStr s ++ divLn ++ mkStatesStr ss
  where divLn = "\n--------------\n"

