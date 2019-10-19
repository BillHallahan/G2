{-# LANGUAGE FlexibleContexts #-}

module G2.Liquid.Inference.PolyRef (extractPolyBound) where

import G2.Language

extractPolyBound :: ASTContainer m Expr => m -> [Expr]
extractPolyBound = evalContainedASTs extractPolyBound'

-- | Given an Apped Data Expr, extracts all arguments bound to polymorphic variables, recursively
extractPolyBound' :: Expr -> [Expr]
extractPolyBound' e =
    let
        es = extractDirectlyPolyBound e
    in
    es ++ concatMap extractPolyBound es

-- | Given an Apped Data Expr, extracts all arguments bound to polymorphic variables
extractDirectlyPolyBound :: Expr -> [Expr]
extractDirectlyPolyBound e
    | Data dc:xs <- filter isType $ unApp e
    , ts <- tyAppArgs $ inTyForAlls $ typeOf dc =
        map snd . filter (isTyVar . fst) $ zip ts xs
    | otherwise = []
    where
        isType (Type _) = True
        isType _ = False