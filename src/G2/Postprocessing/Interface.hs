{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.Interface (runPostprocessing) where

import G2.Language
import G2.Postprocessing.NameSwitcher

runPostprocessing :: Named m => Bindings -> m -> m
runPostprocessing b = switchNames b

