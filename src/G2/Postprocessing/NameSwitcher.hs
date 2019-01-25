{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.NameSwitcher (switchNames) where

import G2.Language

switchNames :: Named m => Bindings -> m -> m
switchNames b e = renames (cleaned_names b) e
