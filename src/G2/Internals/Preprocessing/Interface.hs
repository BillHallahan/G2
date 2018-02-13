{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language
import G2.Internals.Preprocessing.NameCleaner
import G2.Internals.Preprocessing.WrapInteger

runPreprocessing :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> State t
runPreprocessing = cleanNames . wrapInteger