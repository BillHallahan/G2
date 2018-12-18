{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.NameSwitcher (switchNames) where

import G2.Language

switchNames :: Named m => State t -> m -> m
switchNames s e = renames (cleaned_names s) e
