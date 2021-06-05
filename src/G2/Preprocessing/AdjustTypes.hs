{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Preprocessing.AdjustTypes (adjustTypes) where

import G2.Language.AST
import G2.Language

adjustTypes :: ASTContainer t Expr => State t -> State t
adjustTypes = wrapInteger . unpackString

-- | wrapInteger
-- GHC may represent an Integer as:
-- ((fromInteger [Dict]) LitInt)
-- Which makes it hard for us to correctly implement fromInteger in G2.
-- So we put in our Prelude:
-- data Integer = Integer Int#
-- and change ((fromInteger [Dict]) LitInteger) to:
-- ((fromInteger [Dict]) (dcInteger LitInt))
wrapInteger :: ASTContainer t Expr => State t -> State t
wrapInteger s@(State {known_values = kv, type_env = tenv}) = modifyASTs (wrapInteger' (mkDCInteger kv tenv)) s

wrapInteger' :: Expr -> Expr -> Expr
wrapInteger' dcIntgr (Lit (LitInteger i)) = App dcIntgr (Lit . LitInt $ fromInteger i)
wrapInteger' _ e = e

-- | GHC may represent strings as:
-- (App 
--      (Var 
--          (Id 
--              (Name "$unpackCString" (Just "GHC.CString") 0) 
--              (TyFun (TyCon (Name "Addr#" (Just "GHC.Prim") 3674937295934324738) []) (TyCon (Name "$" (Just "GHC.Types") 0) [TyCon (Name "Char" (Just "GHC.Types") 8214565720323798834) []]))
--          )
--      ) 
--      (Lit (LitString "\"HERE\""))
-- )
-- We remove $unpackCString, and convert the LitString to a list
unpackString :: ASTContainer t Expr => State t -> State t
unpackString s@(State {type_env = tenv, known_values = kv}) = modifyASTs (unpackString' tenv kv) s

unpackString' :: TypeEnv -> KnownValues -> Expr -> Expr
unpackString' tenv kv (App (Var (Id (Name "unpackCString#" _ _ _) _)) e) = unpackString' tenv kv e
unpackString' tenv kv (Lit (LitString s)) = 
    let
        cns = App (mkCons kv tenv) (Type (tyChar kv))
        em = App (mkEmpty kv tenv) (Type (tyChar kv))

        char = mkDCChar kv tenv
    in
    foldr App em $ map (App cns . App char . Lit . LitChar) s
unpackString' _ _ e = e
