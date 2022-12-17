module Combined (call) where

import Data.List (minimumBy)

data C k = C k
data Map k = Assocs (C k)

{-@ call :: Map {v:Bool | v } @-}
call   :: Map Bool
call = noAbs (f True)

f :: Bool -> Bool
f c = c

noAbs :: k -> Map k
noAbs k = Assocs (C k)
