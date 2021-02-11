{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE DeriveGeneric #-}

module Combined where


type Center  = Int

{-@ f :: Center @-}
f   :: Center
f = g

{-@ g :: Center @-}
g    :: Center
g = 1