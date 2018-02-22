{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Preprocessing.Interface where

import G2.Internals.Language
import G2.Internals.Preprocessing.NameCleaner
import G2.Internals.Preprocessing.AdjustTypes

runPreprocessing :: (ASTContainer h Expr, ASTContainer t Expr, ASTContainer h Type, ASTContainer t Type, Named h, Named t) => State h t -> State h t
runPreprocessing = cleanNames . adjustTypes