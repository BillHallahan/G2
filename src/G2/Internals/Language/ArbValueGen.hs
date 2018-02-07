module G2.Internals.Language.ArbValueGen ( ArbValueGen
                                         , arbValueInit
                                         , arbValue) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import Data.Coerce
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid

data ArbValueGen = ArbValueGen { intGen :: Int
                               , floatGen :: Rational
                               , doubleGen :: Rational
                               , boolGen :: Bool
                               } deriving (Show, Eq, Read)

arbValueInit :: ArbValueGen
arbValueInit = ArbValueGen { intGen = 0
                           , floatGen = 0
                           , doubleGen = 0
                           , boolGen = True}

-- | arbValue
-- Allows the generation of arbitrary values of the given type.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValue :: Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue (TyConApp n _) tenv av =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADT tenv adt av)
          (M.lookup n tenv)
arbValue TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt $ i), av { intGen = i + 1 })
arbValue TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat $ f), av { floatGen = f + 1 })
arbValue TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble $ d), av { doubleGen = d + 1 })
arbValue _ _ av = (Prim Undefined TyBottom, av)-- error $ "Bad type in arbValue: " ++ show t

-- | numArgs
numArgs :: DataCon -> Int
numArgs = length . dataConArgs

minArgLen :: [DataCon] -> DataCon
minArgLen = minimumBy (\dc dc' -> numArgs dc `compare` numArgs dc')

minArgLenADT :: AlgDataTy -> DataCon
minArgLenADT = minArgLen . dataCon

-- | numRecArgs
-- Just the minimum number of constructors that must exist below the current DataCon
-- or Nothing if there is no such number (the number of constructors must be infinite)
numRecArgsADT :: TypeEnv -> AlgDataTy -> Maybe Int
numRecArgsADT = coerce . numRecArgsADT' []

numRecArgsADT' :: [Name] -> TypeEnv -> AlgDataTy -> Maybe (Sum Int)
numRecArgsADT' ns tenv adt 
    | dc <- minArgLenADT adt
    , numArgs dc == 0 = Just $ Sum 0
    | dcs <- filter ( noTyConsNamed ns . dataConArgs) $ dataCon adt
    , i <- minimum 
            $ mapMaybe ( mconcat 
                       . mapMaybe (\n -> fmap (numRecArgsADT' (n:ns) tenv) $ M.lookup n tenv)
                       . mapMaybe tyConAppName
                       . dataConArgs) dcs =
        Just i
    | otherwise = Nothing

tyConAppName :: Type -> Maybe Name
tyConAppName (TyConApp n _) = Just n
tyConAppName _ = Nothing

getADT :: TypeEnv -> AlgDataTy -> ArbValueGen -> (Expr, ArbValueGen)
getADT = getADT' []

getADT' :: [Name] -> TypeEnv -> AlgDataTy -> ArbValueGen -> (Expr, ArbValueGen)
getADT' ns tenv adt av
    | dc <- minArgLenADT adt
    , numArgs dc == 0
        = (Data dc, av)
    | dcs <- filter (noTyConsNamed ns . dataConArgs) $ dataCon adt
    , Just dc <- minimumByMaybe (\x y -> snd x ` compare` snd y) $ map (scoreTuple tenv) dcs
        =
        let
            es = map (\t -> fst $ arbValue t tenv av) . dataConArgs $ fst dc
            e = foldl' App (Data $ fst dc) es
        in
        (e, av)
    | otherwise = (Prim Undefined TyBottom, av)

minimumByMaybe :: (a -> a -> Ordering) -> [a] -> Maybe a
minimumByMaybe _ [] = Nothing
minimumByMaybe f xs = Just $ minimumBy f xs

noTyConsNamed :: [Name] -> [Type] -> Bool
noTyConsNamed ns = not . any (flip elem ns) . mapMaybe tyConAppName

-- minConsTyCon :: TypeEnv -> [DataCon] -> DataCon
-- minConsTyCon tenv dc =
--     let
--         scored = mapMaybe (scoreTuple tenv) dc
--     in
--     undefined

scoreTuple :: TypeEnv -> DataCon -> (DataCon, Int)
scoreTuple tenv dc = 
    let
        score = mconcat
              . catMaybes
              . (coerce :: ([Maybe Int] -> [Maybe (Sum Int)]))
              . mapMaybe (\n -> fmap (numRecArgsADT tenv) $ M.lookup n tenv) 
              . mapMaybe tyConAppName
              . dataConArgs $ dc
    in
    (dc, coerce score)