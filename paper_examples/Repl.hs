module Repl where

import Prelude hiding ((!))

-- Example from Figure 2 in the paper.
-- repl_prop is a (incorrect) property to be tested about repl.
-- By running G2 on repl_prop with the extra flag --returns-true,
-- a counterexample can be found.

(!) :: [a] -> Int -> a
xs ! j = case xs of
            h:t -> case j == 0 of
                        True -> h
                        False -> t ! (j - 1)

repl :: Int -> [Int]
repl x = x:repl (x + 1)

repl_prop :: Int -> Int -> Bool
repl_prop i k = repl i ! k == i
