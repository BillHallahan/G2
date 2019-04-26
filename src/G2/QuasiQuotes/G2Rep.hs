-- Hides the warnings about deriving 
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.QuasiQuotes.G2Rep ( G2Rep (..)
                            , derivingG2Rep ) where

import G2.QuasiQuotes.Internals.G2Rep

-- Prelude types
$(derivingG2Rep ''Bool)
$(derivingG2Rep ''Maybe)
$(derivingG2Rep ''Either)
$(derivingG2Rep ''Ordering)
-- $(derivingG2Rep ''Char)
$(derivingG2RepTuple 0)
$(derivingG2RepTuples 2 16)
$(derivingG2Rep ''Int)
-- $(derivingG2Rep ''Integer)
$(derivingG2Rep ''Float)
$(derivingG2Rep ''Double)
-- $(derivingG2Rep ''Rational)
-- $(derivingG2Rep ''Word)

$(derivingG2Rep ''[])