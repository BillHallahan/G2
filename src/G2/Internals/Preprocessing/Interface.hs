{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language
import G2.Internals.Preprocessing.NameCleaner
import G2.Internals.Preprocessing.AdjustTypes

runPreprocessing :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> State t
runPreprocessing = cleanNames . adjustTypes