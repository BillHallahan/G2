{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.Parametric (instantiating) where

import G2.Language

import GHC.Generics (Generic)
import Data.Data
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Tuple.Extra

import Debug.Trace

-- | Either an argument or the return value of a function.
data Param = Arg Name Int | Ret Name deriving (Eq, Show, Generic, Typeable, Data)

instance Hashable Param

-- | Determine which function parameters are consistently instantiating a single polymorphic variable.
-- Returns a map from function `Param`s to `Name`s of instantiated polymorphic variables
instantiating :: Expr -> HM.HashMap Param Name
instantiating = instantiating' HM.empty

instantiating' :: HM.HashMap Name Expr -> Expr -> HM.HashMap Param Name
instantiating' binds let_e@(Let l_binds e) =
    let
        binds' = foldr (uncurry HM.insert) binds $ map (\(i, le) -> (idName i, le)) l_binds
    in
    foldr HM.union HM.empty . map (instantiating' binds') $ children let_e
instantiating' binds app@(App _ _) | (Var (Id n t)):es <- unApp app =
    let
        ts = argumentTypes $ PresType t
        ts_es = filter (not . isTYPE . fst) . filter (not . isLHDict . fst) $ zip ts es
        i_ts_es = zipWith (\i (ts, es) -> (i, ts, es)) [1 :: Int ..] ts_es

        higher_ord = map (\(i, t, e) -> (i, t, inline binds e)) $ filter (isTyFun . snd3) i_ts_es

        m = HM.empty
        ms = map (instantiating' binds) es
    in
    trace ("-----\nn = " ++ show n ++ "\nhigher_ord = " ++ show higher_ord) foldr HM.union m ms
    where
        isLHDict t
          | (TyCon (Name n _ _ _) _):_ <- unTyApp t = n == "lh"
          | otherwise = False
instantiating' binds e = foldr HM.union HM.empty . map (instantiating' binds) $ children e

inline :: HM.HashMap Name Expr -> Expr -> Expr
inline h = inline' h HS.empty

inline' :: HM.HashMap Name Expr -> HS.HashSet Name -> Expr -> Expr
inline' h ns v@(Var (Id n _))
    | HS.member n ns = v
    | Just e <- HM.lookup n h = inline' h (HS.insert n ns) e
inline' h ns e = modifyChildren (inline' h ns) e
