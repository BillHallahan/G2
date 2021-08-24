{-# LANGUAGE OverloadedStrings #-}

module G2.Language.ArbValueGen ( ArbValueGen
                               , ArbValueFunc
                               , arbValueInit
                               , arbValue
                               , arbValueInfinite
                               , constArbValue ) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing

import Data.List
import qualified Data.Map as M
import Data.Ord
import Data.Tuple

arbValueInit :: ArbValueGen
arbValueInit = ArbValueGen { intGen = 0
                           , floatGen = 0
                           , doubleGen = 0
                           , charGen = charGenInit -- See [CharGenInit]
                           , boolGen = True
                           }

type ArbValueFunc = Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)

-- [CharGenInit]
-- Do NOT make this a cycle.  It would simplify arbValue, but causes an infinite loop
-- when we have to output a State (in the QuasiQuoter, for example)

charGenInit :: [Char]
charGenInit = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']

-- | arbValue
-- Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValue :: Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue t = arbValue' getFiniteADT M.empty t


-- | arbValue
-- Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that is identical to the passed ArbValueGen
constArbValue :: Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue = constArbValue' getFiniteADT M.empty

-- | arbValue
-- Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite t = arbValueInfinite' M.empty t

arbValueInfinite' :: M.Map Name Type -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite' = arbValue' getADT

arbValue' :: GetADT
          -> M.Map Name Type -- ^ Maps TyVar's to Types
          -> Type
          -> TypeEnv
          -> ArbValueGen
          -> (Expr, ArbValueGen)
arbValue' getADTF m (TyFun t t') tenv av =
    let
      (e, av') = arbValue' getADTF m t' tenv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av')
arbValue' getADTF m t tenv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF m tenv av adt ts)
          (M.lookup n tenv)
arbValue' getADTF m (TyApp t1 t2) tenv av =
  let
      (e1, av') = arbValue' getADTF m t1 tenv av
      (e2, av'') = arbValue' getADTF m t2 tenv av'
  in
  (App e1 e2, av'')
arbValue' _ _ TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt $ i), av { intGen = i + 1 })
arbValue' _ _ TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat $ f), av { floatGen = f + 1 })
arbValue' _ _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble $ d), av { doubleGen = d + 1 })
arbValue' _ _ TyLitChar _ av =
    let
        c:cs = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av { charGen = cs})
arbValue' getADTF m (TyVar (Id n _)) tenv av
    | Just t <- M.lookup n m = arbValue' getADTF m t tenv av
arbValue' _ _ t _ av = (Prim Undefined t, av)


constArbValue' :: GetADT -> M.Map Name Type -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue' getADTF m (TyFun t t') tenv av =
    let
      (e, _) = constArbValue' getADTF m t' tenv av
    in
    (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, av)
constArbValue' getADTF m t tenv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF m tenv av adt ts)
          (M.lookup n tenv)
constArbValue' getADTF m (TyApp t1 t2) tenv av =
  let
      (e1, _) = constArbValue' getADTF m t1 tenv av
      (e2, _) = constArbValue' getADTF m t2 tenv av
  in
  (App e1 e2, av)
constArbValue' _ _ TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt $ i), av)
constArbValue' _ _ TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat $ f), av)
constArbValue' _ _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble $ d), av)
constArbValue' _ _ TyLitChar _ av =
    let
        c:_ = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av)
constArbValue' getADTF m (TyVar (Id n _)) tenv av
    | Just t <- M.lookup n m = constArbValue' getADTF m t tenv av
constArbValue' _ _ t _ av = (Prim Undefined t, av)

type GetADT = M.Map Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)

-- Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr
getFiniteADT :: M.Map Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getFiniteADT m tenv av adt ts =
    let
        (e, av') = getADT m tenv av adt ts
    in 
    (cutOff [] e, av')

cutOff :: [Name] -> Expr -> Expr
cutOff ns a@(App _ _)
    | Data (DataCon n _) <- appCenter a =
        case length (filter (== n) ns) > 3 of
            True -> Prim Undefined TyBottom
            False -> mapArgs (cutOff (n:ns)) a
cutOff _ e = e

-- | Generates an arbitrary value of the given AlgDataTy
-- If there is no such finite value, this may return an infinite Expr
getADT :: M.Map Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getADT m tenv av adt ts 
    | dcs <- dataCon adt
    , _:_ <- dcs =
        let
            ids = boundIds adt

            -- Finds the DataCon for adt with the least arguments
            min_dc = minimumBy (comparing (length . dataConArgs)) dcs

            tyVIds = map TyVar ids
            m' = foldr (uncurry M.insert) m $ zip (map idName ids) ts

            (av', es) = mapAccumL (\av_ t -> swap $ arbValueInfinite' m' t tenv av_) av $ dataConArgs min_dc
        in
        (mkApp $ Data min_dc:map Type ts ++ es, av')
    | otherwise = (Prim Undefined TyBottom, av)
