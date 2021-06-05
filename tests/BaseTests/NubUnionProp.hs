module NubUnionProp where

import Data.List

-- An (incorrect) property about nub and union
prop_nub_union :: Eq a => [a] -> Bool
prop_nub_union xs = nub xs == union xs xs