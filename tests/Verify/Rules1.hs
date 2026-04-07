module Rules1 where

import Prelude hiding (map)

just :: Int -> Maybe Int
{-# NOINLINE just #-}
just n = Just n

polyJust :: a -> Maybe a
{-# NOINLINE polyJust #-}
polyJust n = Just n

{-# RULES
"justJust" forall n . just n = Just n
"justJust2" forall . just = Just
"polyJustJust" forall n . polyJust n = Just n
#-}