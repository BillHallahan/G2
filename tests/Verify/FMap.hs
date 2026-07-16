module FMap where

import Prelude hiding (map)
import qualified Prelude as P

prop :: (X -> X) -> (X -> X) -> [X] -> Bool
prop f g xs = P.map g xs == P.map f xs

data X = X

instance Eq X where
    X == X = True
