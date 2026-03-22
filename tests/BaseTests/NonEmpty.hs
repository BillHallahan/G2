module NonEmpty where

import Prelude hiding (map)
import Data.List.NonEmpty

callMap :: NonEmpty (Int, Int) -> (NonEmpty Int, NonEmpty Int)
callMap xs = (map fst xs, map snd xs)