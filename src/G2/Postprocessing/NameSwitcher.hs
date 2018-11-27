{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.NameSwitcher (switchNames) where

import G2.Language
import qualified Data.Map as M

switchNames :: Named m => State t -> m -> m
switchNames s e = foldr (uncurry rename) e $ M.toList (cleaned_names s)
