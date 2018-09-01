module G2.Internals.Language.ArbValueGen ( ArbValueGen
                                         , arbValueInit
                                         , arbValue) where

import G2.Internals.Language.AST
import G2.Internals.Language.Expr
import G2.Internals.Language.Support
import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv
import G2.Internals.Language.Typing

import Data.Coerce
import Data.List
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.Tuple

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
arbValue t tenv av
  | TyConApp n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (Prim Undefined TyBottom, av) 
          (\adt -> getFiniteADT tenv av adt ts)
          (M.lookup n tenv)
arbValue (TyApp t1 t2) tenv av =
  let
      (e1, av') = arbValue t1 tenv av
      (e2, av'') = arbValue t2 tenv av'
  in
  (App e1 e2, av'')
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

-- Generates an arbitrary value of the given ADT,
-- but will return Undefined instead of an infinite Expr
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
cutOff ns e = e

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

        (es, _) = unzip $ map (\t -> arbValue t tenv av) $ dataConArgs min_dc 
    in
    (mkApp $ Data min_dc':es, av)
