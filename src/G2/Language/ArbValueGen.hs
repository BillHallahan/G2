{-# LANGUAGE BangPatterns, MultiWayIf, OverloadedStrings, RankNTypes #-}

module G2.Language.ArbValueGen ( ArbValueGen
                               , ArbValueFunc
                               , ArbValueFuncM
                               , arbValueInit
                               , arbValue
                               , arbValueInfinite
                               , constArbValue ) where

import G2.Data.Utils
import G2.Language.Expr
import G2.Language.Monad.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import qualified G2.Language.TyVarEnv as TV 
import G2.Language.KnownValues

import Control.Monad (foldM)
import Control.Monad.Extra
import qualified Control.Monad.State.Lazy as SM
import Control.Exception (assert)
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.Maybe as MA
import Data.Ord
import Data.Traversable

-- | A default `ArbValueGen`.
arbValueInit :: ArbValueGen
arbValueInit = ArbValueGen { intGen = 0
                           , floatGen = 0
                           , doubleGen = 0
                           , rationalGen = 0
                           , charGen = charGenInit -- See [CharGenInit]
                           , boolGen = True
                           }

type ArbValueFunc = forall t . State t -> NameGen -> Type -> ArbValueGen -> (Expr, TyVarEnv, ArbValueGen, NameGen)
type ArbValueFuncM = forall t . State t -> Type -> ArbValueGen -> NameGenM (Expr, TyVarEnv, ArbValueGen)

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
arbValue :: ArbValueFunc
arbValue s ng t avg =
    let ((e, tv_env, avg'), ng') = SM.runState (arbValue' getFiniteADT HM.empty s t avg) ng in
    (e, tv_env, avg', ng')

-- | Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that is identical to the passed ArbValueGen
constArbValue :: ArbValueFunc
constArbValue s ng t avg =
    let ((e, tv_env, avg'), ng') = SM.runState (constArbValue' getFiniteADT HM.empty s t avg) ng in
    (e, tv_env, avg', ng')

-- | Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: ArbValueFunc
arbValueInfinite s ng t avg =
    let ((e, tv_env, avg'), ng') = SM.runState (arbValueInfinite' cutOffVal HM.empty s t avg) ng in
    (e, tv_env, avg', ng')

arbValueInfinite' :: Int -> HM.HashMap Name Type -> ArbValueFuncM
arbValueInfinite' !cutoff = arbValue' (getADT cutoff)

arbValue' :: GetADT
          -> HM.HashMap Name Type -- ^ Maps TyVar's to Types
          -> ArbValueFuncM
arbValue' getADTF m s (TyFun t t') av = do
    (e, tv_env, av') <- arbValue' getADTF m s t' av
    return (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, tv_env, av')
arbValue' getADTF m s@(State { type_env = tenv, tyvar_env = tv_env }) t av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (return (Prim Undefined TyBottom, tv_env, av))
          (\adt -> getADTF m s av adt ts)
          (HM.lookup n tenv)
arbValue' getADTF m s (TyApp t1 t2) av = do
    (e1, tv_env, av') <- arbValue' getADTF m s t1 av
    (e2, tv_env', av'') <- arbValue' getADTF m (s { tyvar_env = tv_env }) t2 av'
    return (App e1 e2, tv_env', av'')
arbValue' _ _ (State { tyvar_env = tv_env }) TyLitInt av =
    let
        i = intGen av
    in
    return (Lit (LitInt i), tv_env, av { intGen = i + 1 })
arbValue' _ _ (State { tyvar_env = tv_env }) TyLitFloat av =
    let
        f = floatGen av
    in
    return (Lit (LitFloat f), tv_env, av { floatGen = f + 1 })
arbValue' _ _ (State { tyvar_env = tv_env }) TyLitDouble av =
    let
        d = doubleGen av
    in
    return (Lit (LitDouble d), tv_env, av { doubleGen = d + 1 })
arbValue' _ _ (State { tyvar_env = tv_env }) TyLitRational av =
    let
        r = rationalGen av
    in
    return (Lit (LitRational r), tv_env, av { rationalGen = r + 1 })
arbValue' _ _ (State { tyvar_env = tv_env }) TyLitChar av =
    let
        c:cs = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    return (Lit (LitChar c), tv_env, av { charGen = cs})
arbValue' getADTF m s@(State { tyvar_env = tv }) (TyVar (Id n _)) av
    | Just t <- HM.lookup n m = arbValue' getADTF m s t av
    | Just t@(TyVar _) <- TV.deepLookupName tv n = return (Prim Undefined t, tv, av)
    | Just t <- TV.deepLookupName tv n = arbValue' getADTF m s t av
arbValue' _ _ (State { tyvar_env = tv_env }) t av = return (Prim Undefined t, tv_env, av)

constArbValue' :: GetADT -> HM.HashMap Name Type -> ArbValueFuncM
constArbValue' getADTF m s (TyFun t t') av = do
    (e, tv_env, _) <- constArbValue' getADTF m s t' av
    return (Lam TermL (Id (Name "_" Nothing 0 Nothing) t) e, tv_env, av)
constArbValue' getADTF m s@(State { type_env = tenv, tyvar_env = tv_env }) t av
  | TyCon n _ <- tyAppCenter t
  , ts <- tyAppArgs t =
    maybe (return (Prim Undefined TyBottom, tv_env, av) )
          (\adt -> getADTF m s av adt ts)
          (HM.lookup n tenv)
constArbValue' getADTF m s (TyApp t1 t2) av = do
  (e1, tv_env, _) <- constArbValue' getADTF m s t1 av
  (e2, tv_env', _) <- constArbValue' getADTF m (s { tyvar_env = tv_env }) t2 av
  return (App e1 e2, tv_env', av)
constArbValue' _ _ (State { tyvar_env = tv_env }) TyLitInt av =
    let
        i = intGen av
    in
    return (Lit (LitInt i), tv_env, av)
constArbValue' _ _ (State { tyvar_env = tv_env }) TyLitFloat av =
    let
        f = floatGen av
    in
    return (Lit (LitFloat f), tv_env, av)
constArbValue' _ _ (State { tyvar_env = tv_env }) TyLitDouble av =
    let
        d = doubleGen av
    in
    return (Lit (LitDouble d), tv_env, av)
constArbValue' _ _ (State { tyvar_env = tv_env }) TyLitRational av =
    let
        r = rationalGen av
    in
    return (Lit (LitRational r), tv_env, av)
constArbValue' _ _ (State { tyvar_env = tv_env }) TyLitChar av =
    let
        c:_ = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    return (Lit (LitChar c), tv_env, av)
constArbValue' getADTF m s@(State { tyvar_env = tv }) (TyVar (Id n _)) av
    | Just t <- HM.lookup n m = constArbValue' getADTF m s t av
    | Just t@(TyVar _) <- TV.deepLookupName tv n = return (Prim Undefined t, tv, av)
    | Just t <- TV.deepLookupName tv n = arbValue' getADTF m s t av
constArbValue' _ _ (State { tyvar_env = tv }) t av = return (Prim Undefined t, tv, av)

type GetADT = forall t . HM.HashMap Name Type -> State t -> ArbValueGen -> AlgDataTy -> [Type] -> NameGenM (Expr, TyVarEnv, ArbValueGen)

-- | Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr.
getFiniteADT :: HM.HashMap Name Type -> State t -> ArbValueGen -> AlgDataTy -> [Type] -> NameGenM (Expr, TyVarEnv, ArbValueGen)
getFiniteADT m s av adt ts = do
    (e, tv_env, av') <- getADT cutOffVal m s av adt ts
    return (cutOff [] e, tv_env, av')

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
getADT :: Int -> HM.HashMap Name Type -> State t -> ArbValueGen -> AlgDataTy -> [Type] -> NameGenM (Expr, TyVarEnv, ArbValueGen)
getADT !cutoff m s@(State { tyvar_env = tvnv, known_values = kv }) av adt ts 
    | [dc] <- dataCon adt
    , TyApp (TyApp (TyApp (TyApp (TyCon tc_n _) _) _) c1) c2 <- returnType (typeOf tvnv dc)
    , tc_n == tyCoercion kv = return (Coercion (c1 :~ c2), tvnv, av)
    | dcs <- dataCon adt
    , _:_ <- dcs = do
        let ids = bound_ids adt

            -- Finds the DataCon for adt with the least arguments
        dcs' <- mapMaybeM checkDC dcs

        let (min_dc, tvnv') = minimumBy (comparing (length . anonArgumentTypes . typeOf tvnv . fst)) dcs'

            m' = foldr (uncurry HM.insert) m $ zip (map idName ids) ts

        ((tvnv'', av'), es) <- mapAccumM
                        (\(tvnv_, av_) t -> 
                            if | 0 <= cutoff -> do
                                    (e', tvnv_', av_') <- arbValueInfinite' (cutoff - 1) m' (s { tyvar_env = tvnv_ }) (applyTypeHashMap m' t) av_
                                    return ((tvnv_', av_'), e')
                               | otherwise -> return ((tvnv_, av_), Prim Undefined TyBottom)
                        )
                        (tvnv', av) 
                    $ anonArgumentTypes (typeOf tvnv' min_dc)

        let final_av = if cutoff >= 0 then av' else av
        return (mkApp $ min_dc:es, tvnv'', final_av)
    | otherwise = return (Prim Undefined TyBottom, tvnv, av)
    where
        -- Figure out which data constructor are compatible with the required type, based on coercions.
        -- Consider:
        -- ```
        -- data Contains a where
        -- CInt :: Contains Int
        -- CBool :: Contains Bool

        -- idCBool :: Contains Bool -> Contains Bool
        -- idCBool x = x
        -- ```
        -- x must be a CBool, not a CInt.  To figure this out, we need to know that the type variable a
        -- has been instantiated with Bool (we learn this from the ts input parameter), that the CBool
        -- constructor has the (ok) coercion (a ~ Bool) and that CInt has the (disallowed) coercion (a ~ Int) 

        checkDC dc = do
            let leading_ty = leadingTyForAllBindings (typeOf tvnv dc)
            
                ts' = tyVarSubst tvnv ts
            (leading_ty', dc') <- doRenamesN (map idName leading_ty) (leading_ty, dc)

            let coer = eval (getCoercions kv) (dc_type dc')

            let unifMapTy = foldM (\uf -> uncurry (unify' uf))
            -- Union the forall type bindings with the passed type arguments
            let forall_unif = unifMapTy tvnv
                            . assert (length leading_ty' >= length ts)
                            $ zip (map TyVar leading_ty') ts'
            -- Incorporate coercions (a ~ Int) into a unification map
            let coer_unif = flip unifMapTy coer =<< forall_unif

            -- Determine required instantiations for type arguments
            case coer_unif of
                Just coer_unif' ->
                    let
                        univ_ty = map (\i -> MA.fromMaybe (TyVar i) (TV.lookup (idName i) coer_unif')) (dc_univ_tyvars dc')
                        exist_ty = map (\i -> MA.fromMaybe (TyVar i) (TV.lookup (idName i) coer_unif')) (dc_exist_tyvars dc')
                    in
                    return $ Just (mkApp $ Data dc':map Type univ_ty ++ map Type exist_ty, coer_unif')
                Nothing -> return Nothing
