{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Preprocessing.WrapInteger (wrapInteger) where

import G2.Internals.Language.AST
import G2.Internals.Language


-- | wrapInteger
-- GHC may represent an Integer as:
-- ((fromInteger [Dict]) LitInt)
-- Which makes it hard for us to correctly implement fromInteger in G2.
-- So we put in our Prelude:
-- data Integer = Integer Int#
-- and change ((fromInteger [Dict]) LitInteger) to:
-- ((fromInteger [Dict]) (dcInteger LitInt))
wrapInteger :: State -> State
wrapInteger s@(State {known_values = kv, type_env = tenv}) = modifyASTs (wrapInteger' (mkDCInteger kv tenv)) s

wrapInteger' :: Expr -> Expr -> Expr
wrapInteger' dcIntgr (Lit (LitInteger i)) = App dcIntgr (Lit . LitInt $ fromInteger i)
wrapInteger' _ e = e