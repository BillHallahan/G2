module TypeClass4 where

import qualified Data.Map as M
import Prelude hiding (map, reduce, concat, foldr, foldr1)

import Data.Coerce

f :: Int
f = length (M.empty :: M.Map Int Int)