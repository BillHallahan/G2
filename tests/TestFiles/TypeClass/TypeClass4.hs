module TypeClass4 where

import qualified Data.Map as M

f :: Int
f = length (M.empty :: M.Map Int Int)