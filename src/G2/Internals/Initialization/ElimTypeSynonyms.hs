{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Initialization.ElimTypeSynonyms where

import G2.Internals.Language

import qualified Data.Map as M

elimTypeSyms :: ASTContainer m Type => TypeEnv -> m -> m
elimTypeSyms tenv = modifyASTs (elimTypeSyms' tenv)

elimTypeSyms' :: TypeEnv -> Type -> Type
elimTypeSyms' tenv t@(TyCon n _) =
    case M.lookup n tenv of
        Just (TypeSynonym {synonym_of = st}) -> st
        _ -> t
elimTypeSyms' _ t = t

elimTypeSymsTEnv :: TypeEnv -> TypeEnv
elimTypeSymsTEnv tenv = elimTypeSyms tenv . M.filter (not . typeSym) $ tenv

typeSym :: AlgDataTy -> Bool
typeSym (TypeSynonym _) = True
typeSym _ = False
