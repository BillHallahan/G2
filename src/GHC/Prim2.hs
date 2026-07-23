-- This module mirrors the LitTableInfo datatype from the base library, so that
-- we can also have the type appear in G2's internals. In particular, see the use
-- in G2.Plugin
module GHC.Prim2 where

data LitTableInfo a b = LTI { lit_table :: !(a -> b)
                            , lt_success :: !Bool
                            , lt_partial :: !(a -> Bool)
                            , lt_is_partial :: !Bool }