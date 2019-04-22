{-# LANGUAGE TemplateHaskell #-}

module G2.Language.G2Rep ( G2Rep (..)
                         , derivingG2Rep ) where

import G2.Language.Internals.G2Rep

$(derivingG2Rep ''[])