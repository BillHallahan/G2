module TypeClass4 where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1)

import Data.Coerce

f :: (Int -> Int) -> Int
f fm = length (g fm)

g   :: (Int -> Int) -> M.Map Int Int
g _ = M.empty