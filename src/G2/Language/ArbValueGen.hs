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
import G2.Language.KnownValues as KV
import Data.List
import qualified Data.HashMap.Lazy as HM
import Data.Ord
import Data.Tuple
import Debug.Trace
import Distribution.Compat.Lens (Lens')

-- | A default `ArbValueGen`.
arbValueInit :: ArbValueGen
arbValueInit = ArbValueGen { intGen = 0
                           , floatGen = 0
                           , doubleGen = 0
                           , rationalGen = 0
                           , charGen = charGenInit -- See [CharGenInit]
                           , boolGen = True
                           }

type ArbValueFunc = Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)

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
arbValue :: KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue kv t tenv = arbValue' getFiniteADT kv HM.empty t tenv

-- | Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that is identical to the passed ArbValueGen
constArbValue :: KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue kv = constArbValue' (getFiniteADT kv) HM.empty

-- | Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite kv t = arbValueInfinite' kv cutOffVal HM.empty t

arbValueInfinite' :: KnownValues -> Int -> HM.HashMap Name Type -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite' cutoff = arbValue' (getADT  cutoff)

arbValue' :: GetADT
          -> KnownValues
          -> HM.HashMap Name Type -- ^ Maps TyVar's to Types
          -> Type
          -> TypeEnv
          -> ArbValueGen
          -> (Expr, ArbValueGen)
arbValue' getADTF kv m (TyFun t t') tenv av =
    let
      (e, av') = arbValue' getADTF kv m t' tenv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av')
arbValue' getADTF kv m t tenv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF kv m tenv av adt ts)
          (HM.lookup n tenv)
arbValue' getADTF kv m (TyApp t1 t2) tenv av =
  let
      (e1, av') = arbValue' getADTF kv m t1 tenv av
      (e2, av'') = arbValue' getADTF kv m t2 tenv av'
  in
  (App e1 e2, av'')
arbValue' _ _ TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt i), av { intGen = i + 1 })
arbValue' _ _ TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat f), av { floatGen = f + 1 })
arbValue' _ _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble d), av { doubleGen = d + 1 })
arbValue' _ _ TyLitRational _ av =
    let
        r = rationalGen av
    in
    (Lit (LitRational r), av { rationalGen = r + 1 })
arbValue' _ _ TyLitChar _ av =
    let
        c:cs = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av { charGen = cs})
arbValue' getADTF kv m (TyVar (Id n _)) tenv av
    | Just t <- HM.lookup n m = arbValue' getADTF kv m t tenv av
arbValue' _ _ t _ av = (Prim Undefined t, av)


constArbValue' :: GetADT -> KnownValues -> HM.HashMap Name Type -> Type -> KnownValues -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue' getADTF kv m (TyFun t t') tenv av =
    let
      (e, _) = constArbValue' getADTF kv m t' tenv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av)
constArbValue' getADTF kv m t tenv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF kv m tenv av adt ts)
          (HM.lookup n tenv)
constArbValue' getADTF kv m (TyApp t1 t2) tenv av =
  let
      (e1, _) = constArbValue' getADTF kv m t1 tenv av
      (e2, _) = constArbValue' getADTF kv m t2 tenv av
  in
  (App e1 e2, av)
constArbValue' _ _ _ TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt i), av)
constArbValue' _ _ _TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat f), av)
constArbValue' _ _ _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble d), av)
constArbValue' _ _ _ TyLitRational _ av =
    let
        r = rationalGen av
    in
    (Lit (LitRational r), av)
constArbValue' _ _ _ TyLitChar _ av =
    let
        c:_ = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av)
constArbValue' getADTF kv m (TyVar (Id n _)) tenv av
    | Just t <- HM.lookup n m = constArbValue' getADTF kv m t tenv av
constArbValue' _ _ _ t _ av = (Prim Undefined t, av)

type GetADT = KnownValues -> HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)

-- | Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr.
getFiniteADT :: KnownValues -> HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getFiniteADT kv m tenv av adt ts =
    let
        (e, av') = getADT kv cutOffVal m tenv av adt ts
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

extractDCTypes :: KnownValues -> Type -> Maybe (Type, Type)
extractDCTypes kv (TyForAll i (TyFun (TyApp(TyApp (TyApp (TyApp (TyCon n t') tyfun) ty) t2) t1) t)) =
    if KV.tyCoercion kv == n 
    then 
        trace("The t1 is " ++ show t1 ++ " The t2 is " ++ show t2)Just (t1, t2)
    else 
        trace("The name is " ++ show n)Nothing
extractDCTypes _ _ = trace("extractDCTypes: pattern match not correct") Nothing 
-- | Generates an arbitrary value of the given AlgDataTy
-- If there is no such finite value, this may return an infinite Expr.
--
-- Has a bit of a hack: will update the ArbValueGen, but only for a limited number of loops.
-- This is to ensure that an ArbValueGen is eventually returned.
-- To see why this is needed, suppose we are returning an infinitely large Expr.
-- This Expr will be returned lazily.  But the return of the ArbValueGen is not lazy-
-- so we must just cut off and return at some point.
getADT :: KnownValues -> Int -> HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getADT kv cutoff m tenv av adt ts 
    | dcs <- dataCon adt
    , _:_ <- dcs =
        let
            ids = bound_ids adt

            -- Finds the DataCon for adt with the least arguments
            -- ideas for the 
            dc_ts = map dc_type dcs 
            dc_ts' = map (extractDCTypes kv) dc_ts
            
            min_dc = minimumBy (comparing (length . anonArgumentTypes)) dcs

            m' = trace("The dc_ts' is " ++ show dc_ts')foldr (uncurry HM.insert) m $ zip (map idName ids) ts

            (av', es) = mapAccumL (\av_ t -> swap $ arbValueInfinite' kv (cutoff - 1) m'  (applyTypeHashMap m' t)  tenv av_) av $ anonArgumentTypes min_dc

            final_av = if cutoff >= 0 then av' else av
        in
        (mkApp $ Data min_dc:map Type ts ++ es, final_av)
    | otherwise = (Prim Undefined TyBottom, av)
