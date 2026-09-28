{-# OPTIONS_GHC -Wno-unused-imports #-}

module Call where

import Lib

import G2.Plugin hiding ((==>))

{-# ANN prop Prop #-}
prop :: Int -> Int -> Bool
prop w x = w === x