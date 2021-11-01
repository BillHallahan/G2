{-# LANGUAGE FlexibleContexts #-}

module G2.Preprocessing.Interface where

import G2.Language
import G2.Preprocessing.AdjustTypes
import G2.Preprocessing.NameCleaner

runPreprocessing :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> Bindings -> (State t, Bindings)
-- runPreprocessing s b = cleanNames (adjustTypes s) b
runPreprocessing s b = (s', b {cleaned_names = cl_names', name_gen = ng'})
    where (s', cl_names', ng') = cleanNames (adjustTypes s) (cleaned_names b) (name_gen b)
