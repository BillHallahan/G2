{-# LANGUAGE OverloadedStrings #-}

module G2.Language.ArbValueGen ( ArbValueGen
                               , ArbValueFunc
                               , arbValueInit
                               , arbValue
                               , arbValueInfinite
                               , constArbValue ) where

import G2.Language.Expr
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.Maybe as MA
import Control.Exception 
import Debug.Trace
import qualified G2.Data.UFMap as UF
import Data.Ord
import Data.Tuple

import Debug.Trace
import Data.Maybe (fromMaybe)
import Control.Monad (foldM)

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
arbValue :: E.ExprEnv -> KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValue eenv kv t tenv gen = arbValue' (getFiniteADT eenv kv) HM.empty t tenv gen

-- | Allows the generation of arbitrary values of the given type.
-- Cuts off recursive ADTs with a Prim Undefined
-- Returns a new ArbValueGen that is identical to the passed ArbValueGen
constArbValue :: E.ExprEnv -> KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
constArbValue eenv kv t tenv gen = constArbValue' (getFiniteADT eenv kv) HM.empty t tenv gen

-- | Allows the generation of arbitrary values of the given type.
-- Does not always cut off recursive ADTs.
-- Returns a new ArbValueGen that (in the case of the primitives)
-- will give a different value the next time arbValue is called with
-- the same Type.
arbValueInfinite :: E.ExprEnv -> KnownValues -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite eenv kv t = arbValueInfinite' eenv kv cutOffVal HM.empty t

arbValueInfinite' :: E.ExprEnv -> KnownValues -> Int -> HM.HashMap Name Type -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
arbValueInfinite' eenv kv cutoff = arbValue' (getADT eenv kv cutoff)

arbValue' :: GetADT
          -> HM.HashMap Name Type -- ^ Maps TyVar's to Types
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
          (HM.lookup n tenv)
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
arbValue' getADTF m (TyVar (Id n _)) tenv av
    | Just t <- HM.lookup n m = arbValue' getADTF m t tenv av
arbValue' _ _ t _ av = (Prim Undefined t, av)


constArbValue' :: GetADT -> HM.HashMap Name Type -> Type -> TypeEnv -> ArbValueGen -> (Expr, ArbValueGen)
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
          (HM.lookup n tenv)
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
    (Lit (LitInt i), av)
constArbValue' _ _ TyLitFloat _ av =
    let
        f = floatGen av
    in
    (Lit (LitFloat f), av)
constArbValue' _ _ TyLitDouble _ av =
    let
        d = doubleGen av
    in
    (Lit (LitDouble d), av)
constArbValue' _ _ TyLitRational _ av =
    let
        r = rationalGen av
    in
    (Lit (LitRational r), av)
constArbValue' _ _ TyLitChar _ av =
    let
        c:_ = case charGen av of
                xs@(_:_) -> xs
                _ -> charGenInit
    in
    (Lit (LitChar c), av)
constArbValue' getADTF m (TyVar (Id n _)) tenv av
    | Just t <- HM.lookup n m = constArbValue' getADTF m t tenv av
constArbValue' _ _ t _ av = (Prim Undefined t, av)

type GetADT = HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)

-- | Generates an arbitrary value of the given ADT,
-- but will return something containing @(Prim Undefined)@ instead of an infinite Expr.
getFiniteADT :: E.ExprEnv -> KnownValues -> HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getFiniteADT eenv kv m tenv av adt ts =
    let
        (e, av') = getADT eenv kv cutOffVal m tenv av adt ts
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
getADT :: E.ExprEnv ->  KnownValues -> Int -> HM.HashMap Name Type -> TypeEnv -> ArbValueGen -> AlgDataTy -> [Type] -> (Expr, ArbValueGen)
getADT eenv kv cutoff m tenv av adt ts
    | [dc] <- dataCon adt
    , TyApp (TyApp (TyApp (TyApp (TyCon tc_n _) _) _) c1) c2 <- returnType dc
    , tc_n == tyCoercion kv = (Coercion (c1 :~ c2), av)
    | dcs <- dataCon adt
    , _:_ <- dcs =
        let
            ids = bound_ids adt

            -- the expr we return will be a good point to start 
            dcs' = MA.mapMaybe (checkDC eenv) dcs

            (min_dc, exist_ty) = minimumBy (comparing (length . anonArgumentTypes . fst)) dcs'

            m' = foldr (uncurry HM.insert) m $ zip (map idName ids) ts

            (av', es) = mapAccumL (\av_ t -> swap $ arbValueInfinite' eenv kv (cutoff - 1) m' (applyTypeHashMap m' t) tenv av_) av $ anonArgumentTypes min_dc

            final_av = if cutoff >= 0 then av' else av
        in
        (mkApp $ Data min_dc:map Type ts ++ map Type exist_ty ++ es, final_av)
    | otherwise = (Prim Undefined TyBottom, av)
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

        checkDC eenv' dc = 
            let
                coer = eval (getCoercions kv) (dc_type dc)

                leading_ty = leadingTyForAllBindings dc

                tyvar_ids = tyVarIds ts  
                ts_tys = map typeOf tyvar_ids
                expr = MA.mapMaybe (flip E.lookup  eenv') (map idName tyvar_ids)
                expr_tys = map typeOf expr 
                -- now do the retyping 
                -- first ziped the list 
                ts' = zip expr_tys ts_tys
                uf_map = foldM (\uf_map' (t1, t2) -> unify' uf_map' t1 t2) UF.empty ts' 
                ts'' = case uf_map of
                            Nothing -> trace("In the nothing case ")ts
                            Just uf_map' -> foldl' (\e (n,t) -> retype (Id n (typeOf t)) t e) ts (HM.toList $ UF.toSimpleMap uf_map')

    
                univ_ty_inst = zip (map TyVar leading_ty) ts''
                -- a'110 bound in the expr environment but we aren't checking it 
                uf_map_univ = foldr (\(c1, c2) m_uf -> (\uf -> unify' uf c1 c2) =<< m_uf)
                                (Just UF.empty)
                                (coer ++ univ_ty_inst)
                exist_name = map idName (dc_exist_tyvars dc)
                
                dc' = uf_map_univ >>= \uf_map -> fmap (\exist ->(dc, exist)) (mapM (flip UF.lookup uf_map) exist_name)
            in
            assert (length leading_ty >= length ts) dc'