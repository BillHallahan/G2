{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Lib where

import G2.Plugin hiding ((==>))

{-# ANN module ("--smt-lists --smt-strings")
    #-}

infix 4 ===
x === y = x == y
