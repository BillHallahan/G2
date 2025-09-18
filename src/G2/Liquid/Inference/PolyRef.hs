{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable#-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module G2.Liquid.Inference.PolyRef ( PolyBound (.. )
                                   , RefNamePolyBound
                                   , ExprPolyBound
                                   , extractExprPolyBoundWithRoot
                                   , extractExprPolyBound
                                   , extractTypePolyBound
                                   , extractTypeAppAndFuncPolyBound

                                   , headValue
                                   , removeHead
                                   , extractValues
                                   , uniqueIds
                                   , mapPB
                                   , filterPB
                                   , allPB
                                   , zipPB
                                   , zipWithPB
                                   , zipWithMaybePB
                                   , zip3PB) where

import G2.Language

import qualified Data.HashMap.Lazy as HM
import Data.List
import Data.Maybe
import qualified G2.Language.TyVarEnv as TV 

type RefNamePolyBound = PolyBound String
type ExprPolyBound = PolyBound [Expr]

type TypePolyBound = PolyBound Type

-- | The subexpressions of an expression corresponding to the polymorphic
-- arguments.  If a polymorphic argument is instantiated with a polymorphic
-- type, these are nested recursively.
data PolyBound v = PolyBound v [PolyBound v] deriving (Eq, Read, Show, Functor, Foldable, Traversable)

-------------------------------
-- ExprPolyBound
-------------------------------

extractExprPolyBoundWithRoot :: TyVarEnv -> Expr -> ExprPolyBound
extractExprPolyBoundWithRoot tv e = PolyBound [e] $ extractExprPolyBound tv e

extractExprPolyBound :: TyVarEnv -> Expr -> [ExprPolyBound]
extractExprPolyBound tv e
    | Data dc:_ <- unApp e =
        let
            bound = leadingTyForAllBindings (typeOf tv dc)
            m = extractExprPolyBound' tv e

            bound_es = map (\i -> HM.lookupDefault [] i m) bound
        in
        map (\es -> PolyBound es (mergeExprPolyBound . transpose $ map (extractExprPolyBound tv) es)) bound_es
    | otherwise = []

mergeExprPolyBound :: [[ExprPolyBound]] -> [ExprPolyBound]
mergeExprPolyBound = mapMaybe (\pb -> case pb of
                                (p:pbb) -> Just $ foldr mergeExprPolyBound' p pbb
                                [] -> Nothing)

mergeExprPolyBound' :: ExprPolyBound -> ExprPolyBound -> ExprPolyBound
mergeExprPolyBound' (PolyBound es1 pb1) (PolyBound es2 pb2) =
    PolyBound (es1 ++ es2) (map (uncurry mergeExprPolyBound') $ zip pb1 pb2)

extractExprPolyBound' :: TyVarEnv ->Expr -> HM.HashMap Id [Expr]
extractExprPolyBound' tv e
    | Data dc:es <- unApp e =
    let
        es' = filter (not . isType) es

        argtys = argumentTypes . inTyForAlls $ typeOf tv dc

        argtys_es = zip argtys es'

        (direct, indirect) = partition fstIsTyVar argtys_es
        direct' =  mapMaybe fstMapTyVar direct
        indirect' = map (uncurry substTypes) indirect

        direct_hm = foldr (HM.unionWith (++)) HM.empty
                        $ map (\(i, e_) -> uncurry HM.singleton (i, e_:[])) direct'
    in
    foldr (HM.unionWith (++)) direct_hm $ map (extractExprPolyBound' tv . adjustIndirectTypes tv) indirect'
    | otherwise = HM.empty
    where
        isType (Type _) = True
        isType _ = False

        fstIsTyVar (TyVar _, _) = True
        fstIsTyVar _ = False

        fstMapTyVar (TyVar i, x) = Just (i, x)
        fstMapTyVar _ = Nothing

substTypes :: Type -> Expr -> Expr
substTypes t e
    | _:ts <- unTyApp t
    , e':es <- unApp e =
        mkApp $ e':substTypes' ts es
substTypes _ e = e

substTypes' :: [Type] -> [Expr] -> [Expr]
substTypes' (t:ts) (Type _:es) = Type t:substTypes' ts es
substTypes' _ es = es

adjustIndirectTypes :: TyVarEnv -> Expr -> Expr
adjustIndirectTypes tv e
    | Data dc:es <- unApp e =
        let
            tyses = filter (isType) es
            tyses' = map (\(Type t) -> t) tyses

            bound = leadingTyForAllBindings (typeOf tv dc)
            bound_tyses = zip bound tyses'
        in
        mkApp $ Data (foldr (uncurry retype) dc $ bound_tyses):es
    | otherwise = e
    where
        isType (Type _) = True
        isType _ = False


-------------------------------
-- TypePolyBound
-------------------------------

-- | Unrolls TyApp'ed args, while also keeping them in the base type
extractTypePolyBound :: Type -> TypePolyBound
extractTypePolyBound t =
    let
        (_:ts) = unTyApp t
    in
    PolyBound t $ map extractTypePolyBound ts

-- | Unrolls TyApp'ed and TyFunc'ed args, while also keeping them in the base type
extractTypeAppAndFuncPolyBound :: Type -> TypePolyBound
extractTypeAppAndFuncPolyBound t@(TyApp _ _) =
    let
        (_:ts) = unTyApp t
    in
    PolyBound t $ map extractTypePolyBound ts
extractTypeAppAndFuncPolyBound t@(TyFun _ _) =
    let
        ts = splitTyFuns t
    in
    PolyBound t $ map extractTypePolyBound ts
extractTypeAppAndFuncPolyBound t = PolyBound t []

-------------------------------
-- Generic PolyBound functions
-------------------------------

headValue :: PolyBound v -> v
headValue (PolyBound v _) = v

removeHead :: PolyBound v -> [PolyBound v]
removeHead (PolyBound _ vs) = vs

extractValues :: PolyBound v -> [v]
extractValues (PolyBound v ps) = v:concatMap extractValues ps

uniqueIds :: PolyBound v -> PolyBound Int
uniqueIds = snd . uniqueIds' 0 

uniqueIds' :: Int -> PolyBound v -> (Int, PolyBound Int)
uniqueIds' n (PolyBound _ ps) =
    let
        (n', ps') = mapAccumR (uniqueIds') (n + 1) ps
    in
    (n', PolyBound n ps')

mapPB :: (a -> b) -> PolyBound a -> PolyBound b
mapPB f (PolyBound v ps) = PolyBound (f v) (map (mapPB f) ps)

filterPB :: (PolyBound a -> Bool) -> PolyBound a -> Maybe (PolyBound a)
filterPB p pb@(PolyBound v xs) =
    case p pb of
        True -> Just $ PolyBound v (mapMaybe (filterPB p) xs)
        False -> Nothing

allPB :: (a -> Bool) -> PolyBound a -> Bool
allPB p = all p . extractValues

zipPB :: PolyBound a -> PolyBound b -> PolyBound (a, b)
zipPB (PolyBound a pba) (PolyBound b pbb) = PolyBound (a, b) (zipWith zipPB pba pbb)

zipWithPB :: (a -> b -> c) -> PolyBound a -> PolyBound b -> PolyBound c
zipWithPB f (PolyBound a pba) (PolyBound b pbb) = PolyBound (f a b) (zipWith (zipWithPB f) pba pbb)

zipWithMaybePB :: (Maybe a -> Maybe b -> c) -> PolyBound a -> PolyBound b -> PolyBound c
zipWithMaybePB f pba pbb = zipWithMaybePB' f (mapPB Just pba) (mapPB Just pbb)

zipWithMaybePB' :: (Maybe a -> Maybe b -> c) -> PolyBound (Maybe a) -> PolyBound (Maybe b) -> PolyBound c
zipWithMaybePB' f (PolyBound a pba) (PolyBound b pbb) =
    let
        c = f a b

        rep_nt = repeat (PolyBound Nothing [])

        pbc = takeWhile (\(x, y) -> isJust (headValue x) || isJust (headValue y))
                $ zip (pba ++ rep_nt) (pbb ++ rep_nt)
    in
    PolyBound c $ map (uncurry (zipWithMaybePB' f)) pbc

zip3PB :: PolyBound a -> PolyBound b -> PolyBound c -> PolyBound (a, b, c)
zip3PB (PolyBound a pba) (PolyBound b pbb) (PolyBound c pbc) =
    PolyBound (a, b, c) (zipWith3 zip3PB pba pbb pbc)
