{-# LANGUAGE FlexibleContexts #-}

module G2.Initialization.ElimTypeSynonyms ( elimTypeSyms
                                          , elimTypeSymsTEnv) where

import G2.Language

import qualified Data.HashMap.Lazy as HM

elimTypeSyms :: ASTContainer m Type => TypeEnv -> m -> m
elimTypeSyms tenv = modifyASTs (elimTypeSyms' tenv)

elimTypeSyms' :: TypeEnv -> Type -> Type
elimTypeSyms' tenv t
    | (TyCon n _) <- tyAppCenter t
    , ts <- tyAppArgs t
    , Just (TypeSynonym { bound_ids = is, synonym_of = st }) <- HM.lookup n tenv
    , length ts == length is =
    -- We recursively call elimTypeSyms, in case a type synonym  maps directly to a type synonym
    elimTypeSyms' tenv $ foldr (uncurry replaceASTs) st $ zip (map TyVar is) ts
elimTypeSyms' _ t = t

elimTypeSymsTEnv :: TypeEnv -> TypeEnv
elimTypeSymsTEnv tenv = elimTypeSyms tenv . HM.filter (not . typeSym) $ tenv

typeSym :: AlgDataTy -> Bool
typeSym (TypeSynonym _ _ _) = True
typeSym _ = False
