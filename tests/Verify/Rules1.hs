module Rules1 where

just :: Int -> Maybe Int
{-# NOINLINE just #-}
just n = Just n

{-# RULES
"justJust" forall n . just n = Just n
#-}