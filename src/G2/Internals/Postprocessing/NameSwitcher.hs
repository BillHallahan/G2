{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Postprocessing.NameSwitcher (switchNames) where

import G2.Internals.Language
import qualified Data.Map as M

switchNames :: Named m => State h t -> m -> m
switchNames s e = foldr (uncurry rename) e $ M.toList (cleaned_names s)