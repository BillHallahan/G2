{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Postprocessing.Interface where

import G2.Internals.Language
import G2.Internals.Postprocessing.NameSwitcher
import G2.Internals.Postprocessing.Undefunctionalize

runPostprocessing :: (ASTContainer m Expr, Named m) => State -> m -> m
runPostprocessing s = undefunctionalize s
				    . switchNames s