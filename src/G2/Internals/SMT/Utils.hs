module G2.Internals.SMT.Utils where

import G2.Internals.SMT.Language

import Data.List

-- | varNames
-- Returns a list of all variable names and sorts used in the given SMTAST Container
varNamesSorts :: ASTContainer m SMTAST => m -> [(Name, Sort)]
varNamesSorts = nub . evalASTs varNamesSorts'
    where
        varNamesSorts' :: SMTAST -> [(Name, Sort)]
        varNamesSorts' (V n s) = [(n, s)]
        varNamesSorts' _ = []