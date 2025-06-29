{-# LANGUAGE OverloadedStrings #-}

module G2.Language.ArbValueGen ( ArbValueGen
                               , ArbValueFunc
                               , arbValueInit
                               , arbValue
                               , arbValueInfinite
                               , constArbValue ) where

import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import Data.List
import qualified Data.HashMap.Lazy as HM
import Data.Ord
import Data.Tuple
import qualified G2.Language.TyVarEnv as TV 
import Debug.Trace
-- | A default `ArbValueGen`.
arbValueInit :: ArbValueGen
arbValueInit = ArbValueGen { intGen = 0
                           , floatGen = 0
                           , doubleGen = 0
                           , rationalGen = 0
                           , charGen = charGenInit -- See [CharGenInit]
                           , boolGen = True
                           }

type ArbValueFunc = Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)

-- [CharGenInit]
-- Do NOT make this a cycle.  It would simplify arbValue, but causes an infinite loop
-- when we have to output a State (in the QuasiQuoter, for example)

charGenInit :: [Char]
charGenInit = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

-- | Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValue :: Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue = arbValue' getFiniteADT HM.empty

-- | Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that is identical to the passed ArbValueGen
constArbValue :: Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue = constArbValue' getFiniteADT HM.empty

-- | Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite t tenv tv = arbValueInfinite' cutOffVal HM.empty t tenv tv

arbValueInfinite' ::  Int -> HM.HashMap Name Type -> Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite' cutoff m t tenv tv = arbValue' (getADT cutoff) m t tenv tv

arbValue' :: GetADT
          -> HM.HashMap Name Type -- ^ Maps TyVar's to Types
          -> Type
          -> TypeEnv
          -> TV.TyVarEnv
          -> ArbValueGen
          -> (Expr, ArbValueGen)
arbValue' getADTF m (TyFun t t') tenv tv av =
    let
      (e, av') = arbValue' getADTF m t' tenv tv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av')
arbValue' getADTF m t tenv tv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF m tenv tv av adt ts)
          (HM.lookup n tenv)
arbValue' getADTF m (TyApp t1 t2) tenv tv av =
  let
      (e1, av') = arbValue' getADTF m t1 tenv tv av
      (e2, av'') = arbValue' getADTF m t2 tenv tv av'
  in
  (App e1 e2, av'')
arbValue' _ _ TyLitInt _ _ av =
    let
        i = intGen av
    in
    (Lit (LitInt i), av { intGen = i + 1 })
arbValue' _ _ TyLitFloat _ _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat f), av { floatGen = f + 1 })
arbValue' _ _ TyLitDouble _ _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble d), av { doubleGen = d + 1 })
arbValue' _ _ TyLitRational _ _ av =
    let
        r = rationalGen av
    in
    (Lit (LitRational r), av { rationalGen = r + 1 })
arbValue' _ _ TyLitChar _ _ av =
    let
        c:cs = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av { charGen = cs})
arbValue' getADTF m (TyVar (Id n _)) tenv tv av
    | Just t <- HM.lookup n m = arbValue' getADTF m t tenv tv av
    | Just t <- TV.lookup n tv = arbValue' getADTF m t tenv tv av
arbValue' _ _ t _ _ av = trace ("arbValue' = " ++ show t) (Prim Undefined t, av)


constArbValue' :: GetADT -> HM.HashMap Name Type -> Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue' getADTF m (TyFun t t') tenv tv av =
    let
      (e, _) = constArbValue' getADTF m t' tenv tv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av)
constArbValue' getADTF m t tenv tv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF m tenv tv av adt ts)
          (HM.lookup n tenv)
constArbValue' getADTF m (TyApp t1 t2) tenv tv av =
  let
      (e1, _) = constArbValue' getADTF m t1 tenv tv av
      (e2, _) = constArbValue' getADTF m t2 tenv tv av
  in
  (App e1 e2, av)
constArbValue' _ _ TyLitInt _ _ av =
    let
        i = intGen av
    in
    (Lit (LitInt i), av)
constArbValue' _ _ TyLitFloat _ _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat f), av)
constArbValue' _ _ TyLitDouble _ _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble d), av)
constArbValue' _ _ TyLitRational _ _ av =
    let
        r = rationalGen av
    in
    (Lit (LitRational r), av)
constArbValue' _ _ TyLitChar _ _ av =
    let
        c:_ = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av)
constArbValue' getADTF m (TyVar (Id n _)) tenv tv av
    | Just t <- HM.lookup n m = constArbValue' getADTF m t tenv tv av
    | Just t <- TV.lookup n tv = arbValue' getADTF m t tenv tv av
constArbValue' _ _ t _ _ av = (Prim Undefined t, av)

type GetADT = HM.HashMap Name Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)

-- | Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr.
getFiniteADT :: HM.HashMap Name Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getFiniteADT m tenv tv av adt ts =
    let
        (e, av') = getADT cutOffVal m tenv tv av adt ts
    in 
    (cutOff [] e, av')

-- | How long to go before cutting off finite ADTs?
cutOffVal :: Int
cutOffVal = 3

cutOff :: [Name] -> Expr -> Expr
cutOff ns a@(App _ _)
    | Data (DataCon n _ _ _) <- appCenter a =
        case length (filter (== n) ns) > cutOffVal of
            True -> Prim Undefined TyBottom
            False -> mapArgs (cutOff (n:ns)) a
cutOff _ e = e

-- | Generates an arbitrary value of the given AlgDataTy
-- If there is no such finite value, this may return an infinite Expr.
--
-- Has a bit of a hack: will update the ArbValueGen, but only for a limited number of loops.
-- This is to ensure that an ArbValueGen is eventually returned.
-- To see why this is needed, suppose we are returning an infinitely large Expr.
-- This Expr will be returned lazily.  But the return of the ArbValueGen is not lazy-
-- so we must just cut off and return at some point.
getADT :: Int -> HM.HashMap Name Type -> TypeEnv -> TV.TyVarEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getADT cutoff m tenv tvnv av adt ts 
    | dcs <- dataCon adt
    , _:_ <- dcs =
        let
            ids = bound_ids adt

            -- Finds the DataCon for adt with the least arguments
            min_dc = minimumBy (comparing (length . anonArgumentTypes. typeOf tvnv)) dcs

            m' = foldr (uncurry HM.insert) m $ zip (map idName ids) ts

            (av', es) = mapAccumL (\av_ t -> swap $ arbValueInfinite' (cutoff - 1) m' (applyTypeHashMap m' t) tenv tvnv av_) av 
                            $ anonArgumentTypes (typeOf tvnv min_dc)

            final_av = if cutoff >= 0 then av' else av
        in
        (mkApp $ Data min_dc:map Type ts ++ es, final_av)
    | otherwise = (Prim Undefined TyBottom, av)
