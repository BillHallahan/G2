{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Sorts (typeToSort) where

import G2.Language

import Language.Fixpoint.Types.Names
import Language.Fixpoint.Types.Sorts
import Language.Fixpoint.Types.Spans

import qualified Data.Text as T

typeToSort :: Type -> Sort
typeToSort (TyCon (Name n _ _ _) _)
    | n == "Int" = FInt
    | n == "Real" = FReal
typeToSort (TyCon n _) = FTC $ symbolFTycon (nameToLocSymbol n)
typeToSort _ = error "typeToSort: type not handled"

nameToLocSymbol :: Name -> LocSymbol
nameToLocSymbol = dummyLoc . nameToSymbol

nameToSymbol :: Name -> Symbol
nameToSymbol (Name n (Just m) _ _) = symbol $ m `T.append` "." `T.append` n
nameToSymbol (Name n Nothing _ _) = symbol n