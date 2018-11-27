{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.Interface where

import G2.Language
import G2.Postprocessing.NameSwitcher
import G2.Postprocessing.Undefunctionalize

runPostprocessing :: (ASTContainer m Expr, Named m) => State t -> m -> m
runPostprocessing s = undefunctionalize s
                    . switchNames s
