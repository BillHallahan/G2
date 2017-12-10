module G2.Internals.Language.ArbValueGen ( ArbValueGen
                                         , arbValueInit
                                         , arbValue) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.TypeEnv

import qualified Data.Map as M

import Debug.Trace

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
arbValue (TyConApp n ts) tenv av = getADTBase n ts tenv av
arbValue TyInt tenv av =
    let
        (i, av') = arbValue TyLitInt tenv av
    in
    (App (Data $ PrimCon I) $ i, av')
arbValue TyFloat tenv av =
    let
        (f, av') = arbValue TyLitFloat tenv av
    in
    (App (Data $ PrimCon F) $ f, av')
arbValue TyDouble tenv av =
    let
        (d, av') = arbValue TyLitDouble tenv av
    in
    (App (Data $ PrimCon D) $ d, av')
arbValue TyLitInt _ av =
    let
        i = intGen av
    in
    (Lit (LitInt $ i), av { intGen = i + 1})
arbValue TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat $ f), av { floatGen = f + 1})
arbValue TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble $ d), av { doubleGen = d + 1})
arbValue TyBool _ av =
    let
        b = boolGen av
    in
    (Lit (LitBool $ b), av { boolGen = not b})
arbValue t _ _ = error $ "Bad type in arbValue: " ++ show t

getADTBase :: Name -> [Type] -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
getADTBase n ts tenv av =
    let
        adt = fmap (retypeAlgDataTy ts) $ M.lookup n tenv

        b = fmap baseDataCons $ getDataCons n tenv
    in
    case b of
        Just (b':_) -> (Data b', av)
        _ ->
            case fmap newTyConRepType adt of
                Just (Just t) -> 
                    let
                        (b', av') = arbValue t tenv av
                    in
                    (Cast b' (t :~ TyConApp n []), av')
                _ -> error $ "getADTBase: No valid base constructor found " ++ show n ++ " " ++ show adt

