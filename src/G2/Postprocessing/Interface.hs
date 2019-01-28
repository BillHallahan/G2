{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.Interface (runPostprocessing) where

import G2.Language
import G2.Postprocessing.NameSwitcher
import G2.Postprocessing.Undefunctionalize

runPostprocessing :: (ASTContainer m Expr, Named m) => State t -> Bindings -> m -> m
runPostprocessing s b = undefunctionalize s b
                    . switchNames b

