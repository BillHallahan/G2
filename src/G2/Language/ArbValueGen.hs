module G2.Language.ArbValueGen ( ArbValueGen
                               , ArbValueFunc
                               , arbValueInit
                               , arbValue
                               , arbValueInfinite ) where

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
arbValue = arbValue' getFiniteADT

-- | arbValue
-- Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite = arbValue' getADT

arbValue' :: GetADT -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue' getADTF t tenv av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getADTF tenv av adt ts)
          (M.lookup n tenv)
arbValue' getADTF (TyApp t1 t2) tenv av =
  let
      (e1, av') = arbValue' getADTF t1 tenv av
      (e2, av'') = arbValue' getADTF t2 tenv av'
  in
  (App e1 e2, av'')
arbValue' _ TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt $ i), av { intGen = i + 1 })
arbValue' _ TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat $ f), av { floatGen = f + 1 })
arbValue' _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble $ d), av { doubleGen = d + 1 })
arbValue' _ TyLitChar _ av =
    let
        c:cs = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av { charGen = cs})
arbValue' _ t _ av = (Prim Undefined t, av)

type GetADT = TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)

-- Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr
getFiniteADT :: TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getFiniteADT tenv av adt ts =
    let
        (e, av') = getADT tenv av adt ts
    in
    (cutOff [] e, av')

cutOff :: [Name] -> Expr -> Expr
cutOff ns a@(App _ _)
    | Data (DataCon n _) <- appCenter a =
        case n `elem` ns of
            True -> Prim Undefined TyBottom
            False -> mapArgs (cutOff (n:ns)) a
cutOff _ e = e

-- | Generates an arbitrary value of the given AlgDataTy
-- If there is no such finite value, this may return an infinite Expr
getADT :: TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getADT tenv av adt ts =
    let
        dcs = dataCon adt
        ids = boundIds adt

        -- Finds the DataCon for adt with the least arguments
        min_dc = minimumBy (comparing (length . dataConArgs)) dcs

        tyVIds = map TyVar ids
        min_dc' = foldr (uncurry replaceASTs) min_dc $ zip tyVIds ts

        -- (av', es) = mapAccumL (\av_ t -> swap $ arbValueInfinite t tenv av_) av $ dataConArgs min_dc'
        es = map (\t -> fst $ arbValueInfinite t tenv av) $ dataConArgs min_dc'
        av' = av
    in
    (mkApp $ Data min_dc':es, av')
