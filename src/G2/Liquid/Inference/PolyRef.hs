{-# LANGUAGE FlexibleContexts #-}

module G2.Liquid.Inference.PolyRef (extractPolyBound) where

import G2.Language

import Data.List
import qualified Data.Map as M
import Debug.Trace

-- | Given an Apped Data Expr, extracts all arguments bound to polymorphic variables
extractPolyBound :: Expr -> M.Map Name [Expr]
extractPolyBound e
    | Data dc:es <- unApp e =
        let
            es' = filter (not . isType) es
            
            binds = zip (leadingTyForAllBindings dc) [1..]
            arg_tys = argumentTypes . PresType . inTyForAlls $ typeOf dc

            (direct, m_indirect) = partition (isTyVar . fst) $ zip arg_tys es'

            direct' = map (\(TyVar i, e) -> (idName i, [e])) direct
            indirect = M.unionsWith (++) $ map (uncurry extractPolyBound')  m_indirect
        in

        M.unionWith (++) (M.fromListWith (++) direct') indirect
    | otherwise = M.empty
    where
        isType (Type _) = True
        isType _ = False

extractPolyBound' :: Type -> Expr -> M.Map Name [Expr]
extractPolyBound' t e = extractPolyBound e