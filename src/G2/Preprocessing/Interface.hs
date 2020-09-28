{-# LANGUAGE FlexibleContexts #-}

module G2.Preprocessing.Interface where

import G2.Language
import qualified G2.Language.ExprEnv as E
import G2.Preprocessing.AdjustTypes
import G2.Preprocessing.NameCleaner

runPreprocessing :: (ASTContainer t Expr, ASTContainer t Type, Named t) => State t -> Bindings -> (State t, Bindings)
runPreprocessing s b = (s'', b {cleaned_names = cl_names', name_gen = ng''})
    where
    	(s', cl_names', ng') = cleanNames (adjustTypes s) (cleaned_names b) (name_gen b)
    	(eenv', ng'') = E.assignCLs ng' (expr_env s')
    	s'' = s' {expr_env = eenv'}