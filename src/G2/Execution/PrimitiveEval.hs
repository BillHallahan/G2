{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Execution.PrimitiveEval ( evalPrimsSharing
                                  , evalPrims
                                  , mutVarTy
                                  , evalPrimWithState
                                  , newMutVar
                                  , maybeEvalPrim
                                  , evalPrimSymbolic) where

import G2.Language.AST
import G2.Language.Expr
import qualified G2.Language.KnownValues as KV
import G2.Language.Naming
import G2.Language.Primitives
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing

import Control.Exception
import Data.Char
import qualified Data.HashMap.Lazy as M
import qualified Data.List as L
import Data.Maybe
import qualified G2.Language.ExprEnv as E
import G2.Language.MutVarEnv

-- | Evaluates primitives at the root of the passed `Expr` while updating the `ExprEnv`
-- to share computed results.
evalPrimsSharing :: ExprEnv -> TypeEnv -> KnownValues -> Expr -> (Expr, ExprEnv)
evalPrimsSharing eenv tenv kv e =
    let (_, e', eenv') = evalPrimsSharing' eenv tenv kv . simplifyCasts $ e in (e', eenv')

-- | Passed back in evalPrimsSharing' to indicate whether a new value has been computed,
-- and thus indicate whether insertion into the `ExprEnv` is needed.
data NeedUpdate = Update | NoUpdate deriving Show

evalPrimsSharing' :: ExprEnv -> TypeEnv -> KnownValues -> Expr -> (NeedUpdate, Expr, ExprEnv)
evalPrimsSharing' eenv tenv kv a@(App _ _) =
    case unApp a of
        p@(Prim _ _):es ->
            let
                (eenv', es') = L.mapAccumR
                                    (\eenv_ e -> let (_, e', eenv_') = evalPrimsSharing' eenv_ tenv kv e in (eenv_', e'))
                                    eenv es
                ev = evalPrim' tenv kv (p:es')
            in
            (Update, ev, eenv')
        v@(Var _):xs | p@(Prim _ _) <- repeatedLookup eenv v -> evalPrimsSharing' eenv tenv kv (mkApp $ p:xs)
        _ -> (NoUpdate, a, eenv)
evalPrimsSharing' eenv tenv kv v@(Var (Id n _)) =
    case E.lookupConcOrSym n eenv of
        Just (E.Conc e) -> case evalPrimsSharing' eenv tenv kv e of
                                (Update, e', eenv') -> (Update, e', E.insert n e' eenv')
                                r@(NoUpdate, _, _) -> r
        _ -> (NoUpdate, v, eenv)
evalPrimsSharing' eenv _ _ e = (NoUpdate, e, eenv)

repeatedLookup :: ExprEnv -> Expr -> Expr
repeatedLookup eenv v@(Var (Id n _))
    | E.isSymbolic n eenv = v
    | otherwise = 
        case E.lookup n eenv of
          Just v'@(Var _) -> repeatedLookup eenv v'
          Just e -> e
          Nothing -> v
repeatedLookup _ e = e

evalPrims :: ASTContainer m Expr => TypeEnv -> KnownValues -> m -> m
evalPrims tenv kv = modifyContainedASTs (evalPrims' tenv kv . simplifyCasts)

evalPrims' :: TypeEnv -> KnownValues -> Expr -> Expr
evalPrims' tenv kv a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim' tenv kv [p, evalPrims' tenv kv l]
        [p@(Prim _ _), l1, l2] ->
            evalPrim' tenv kv [p, evalPrims' tenv kv l1, evalPrims' tenv kv l2]
        _ -> App (evalPrims' tenv kv x) (evalPrims' tenv kv y)
evalPrims' tenv kv e = modifyChildren (evalPrims' tenv kv) e

evalPrim' :: TypeEnv -> KnownValues -> [Expr] -> Expr
evalPrim' tenv kv xs = fromMaybe (mkApp xs) (maybeEvalPrim' tenv kv xs)

maybeEvalPrim :: TypeEnv -> KnownValues -> Expr -> Maybe Expr
maybeEvalPrim tenv kv = maybeEvalPrim' tenv kv . unApp

maybeEvalPrim' :: TypeEnv -> KnownValues -> [Expr] -> Maybe Expr
maybeEvalPrim' tenv kv xs
    | [Prim p _, x] <- xs
    , Lit x' <- x
    , Just e <- evalPrim1 p x' = Just e
    | [Prim p _, x] <- xs
    , Lit x' <- x = evalPrim1' tenv kv p x'

    | [Prim p _, x, y] <- xs
    , Lit x' <- x
    , Lit y' <- y = evalPrim2 kv p x' y'

    | [Prim p _, Type t, dc_e] <- xs, Data dc:_ <- unApp dc_e =
        evalTypeDCPrim2 tenv p t dc

    | [Prim p _, Type t, Lit (LitInt l)] <- xs =
        evalTypeLitPrim2 tenv p t l

    | otherwise = Nothing

-- | Evaluate primitives that need to read from or modify the State.
-- For more on MutVar's Note [MutVar Env] in G2.Language.MutVarEnv.
evalPrimWithState :: State t -- ^ Context to evaluate expression `e` in
                  -> NameGen
                  -> Expr -- ^ The expression `e` to evaluate
                  -> Maybe (State t, NameGen) -- ^ `Just` if `e` is a primitive operation that this function reduces, `Nothing` otherwise
evalPrimWithState s ng (App (Prim HandleGetPos _) hnd)
    | (Prim (Handle n) _) <- deepLookupExprPastTicks hnd (expr_env s)
    , Just (HandleInfo { h_pos = pos }) <- M.lookup n (handles s) = Just (s { curr_expr = CurrExpr Evaluate (Var pos) }, ng)
evalPrimWithState s ng (App (App (Prim HandleSetPos _) (Var new_pos)) hnd)
    | (Prim (Handle n) _) <- deepLookupExprPastTicks hnd (expr_env s)
    , Just hi <- M.lookup n (handles s) =
        let
            s' = s { curr_expr = CurrExpr Evaluate (mkUnit (known_values s) (type_env s))
                   , handles = M.insert n (hi { h_pos = new_pos }) (handles s)}
        in
        Just (s', ng)
evalPrimWithState s ng (App (App (Prim HandlePutChar _) c) hnd)
    | (Prim (Handle n) _) <- deepLookupExprPastTicks hnd (expr_env s)
    , Just hi <- M.lookup n (handles s) =
        let
            pos = h_pos hi
            ty_string = typeOf pos

            (new_pos, ng') = freshSeededId (Name "pos" Nothing 0 Nothing) ty_string ng
            e = mkApp [mkCons (known_values s) (type_env s), Type ty_string, c, Var new_pos]
            s' = s { expr_env = E.insert (idName pos) e (expr_env s)
                   , curr_expr = CurrExpr Evaluate (mkUnit (known_values s) (type_env s))
                   , handles = M.insert n (hi { h_pos = new_pos }) (handles s)}
        in
        Just (s', ng')
evalPrimWithState s ng (App (App (App (App (Prim NewMutVar _) (Type t)) (Type ts)) e) _) = Just $ newMutVar s ng MVConc ts t e
evalPrimWithState s ng (App (App (App (App (Prim ReadMutVar _) _) _) mv_e) _)
    | (Prim (MutVar mv) _) <- deepLookupExprPastTicks mv_e (expr_env s) =
    let
        i = lookupMvVal mv (mutvar_env s)
        s' = maybe (error "evalPrimWithState: MutVar not found")
                   (\i' -> s { curr_expr = CurrExpr Evaluate (Var i') })
                   i
    in
    Just (s', ng)
evalPrimWithState s ng (App (App (App (App (App (Prim WriteMutVar _) _) (Type t)) mv_e) e) pr_s)
    | (Prim (MutVar mv) _) <- deepLookupExprPastTicks mv_e (expr_env s) =
    let
        (i, ng') = freshId t ng
        s' = s { expr_env = E.insert (idName i) e (expr_env s)
               , mutvar_env = updateMvVal mv i (mutvar_env s)
               , curr_expr = CurrExpr Evaluate pr_s }
    in
    Just (s', ng')
evalPrimWithState _ _ e | [Prim WriteMutVar _, _, _, _, _, _] <- unApp e = Nothing
evalPrimWithState _ _ _ = Nothing

deepLookupExprPastTicks :: Expr -> ExprEnv -> Expr
deepLookupExprPastTicks (Var i@(Id n _)) eenv =
    case E.lookupConcOrSym n eenv of
        Just (E.Conc e) -> deepLookupExprPastTicks e eenv
        _ -> Var i
deepLookupExprPastTicks (Tick _ e) eenv = deepLookupExprPastTicks e eenv
deepLookupExprPastTicks e _ = e

mutVarTy :: KnownValues
         -> Type -- ^ The State type
         -> Type -- ^ The stored type
         -> Type
mutVarTy kv ts ta = TyApp (TyApp (TyCon (KV.tyMutVar kv) (TyFun TYPE (TyFun TYPE TYPE))) ts) ta

newMutVar :: State t
          -> NameGen
          -> MVOrigin
          -> Type -- ^ The State type
          -> Type -- ^ The stored type
          -> Expr
          -> (State t, NameGen)
newMutVar s ng org ts t e =
    let
        (mv_n, ng') = freshSeededName (Name "mv" Nothing 0 Nothing) ng
        (i, ng'') = freshId t ng'        
        s' = s { curr_expr = CurrExpr Evaluate (Prim (MutVar mv_n) $ mutVarTy (known_values s) ts t)
               , expr_env = E.insert (idName i) e (expr_env s)
               , mutvar_env = insertMvVal mv_n i org (mutvar_env s)}
    in
    (s', ng'')

evalPrim1 :: Primitive -> Lit -> Maybe Expr
evalPrim1 Negate (LitInt x) = Just . Lit $ LitInt (-x)
evalPrim1 Negate (LitRational x) = Just . Lit $ LitRational (-x)
evalPrim1 FpNeg (LitFloat x) = Just . Lit $ LitFloat (-x)
evalPrim1 FpNeg (LitDouble x) = Just . Lit $ LitDouble (-x)
evalPrim1 Abs (LitInt x) = Just . Lit $ LitInt (abs x)
evalPrim1 Abs (LitRational x) = Just . Lit $ LitRational (abs x)
evalPrim1 Abs (LitFloat x) = Just . Lit $ LitFloat (abs x)
evalPrim1 Abs (LitDouble x) = Just . Lit $ LitDouble (abs x)
evalPrim1 FpSqrt x = evalPrim1Floating sqrt x
evalPrim1 TruncZero (LitFloat x) = Just . Lit $ LitInt (fst $ properFraction x)
evalPrim1 TruncZero (LitDouble x) = Just . Lit $ LitInt (fst $ properFraction x)
evalPrim1 DecimalPart (LitFloat x) = Just . Lit $ LitFloat (snd $ properFraction x)
evalPrim1 DecimalPart (LitDouble x) = Just . Lit $ LitDouble (snd $ properFraction x)
evalPrim1 IntToFloat (LitInt x) = Just . Lit $ LitFloat (fromIntegral x)
evalPrim1 IntToDouble (LitInt x) = Just . Lit $ LitDouble (fromIntegral x)
evalPrim1 IntToRational (LitInt x) = Just . Lit $ LitRational (fromIntegral x)
evalPrim1 Chr (LitInt x) = Just . Lit $ LitChar (chr $ fromInteger x)
evalPrim1 OrdChar (LitChar x) = Just . Lit $ LitInt (toInteger $ ord x)
evalPrim1 WGenCat (LitInt x) = Just . Lit $ LitInt (toInteger . fromEnum . generalCategory . toEnum $ fromInteger x)
evalPrim1 _ _ = Nothing

evalPrim1' :: TypeEnv -> KnownValues -> Primitive -> Lit -> Maybe Expr
evalPrim1' tenv kv IntToString (LitInt x) =
    let
        char_ty = tyChar kv
        char_dc = mkDCChar kv tenv
    in
    Just . mkG2List kv tenv char_ty . map (App char_dc . Lit . LitChar) $ show x
evalPrim1' _ kv FpIsNegativeZero (LitFloat x) = Just . mkBool kv $  isNegativeZero x
evalPrim1' _ kv FpIsNegativeZero (LitDouble x) = Just . mkBool kv $  isNegativeZero x
evalPrim1' _ kv IsNaN (LitFloat x) = Just . mkBool kv $ isNaN x
evalPrim1' _ kv IsNaN (LitDouble x) = Just . mkBool kv $  isNaN x
evalPrim1' _ kv IsInfinite (LitFloat x) = Just . mkBool kv $ isInfinite x
evalPrim1' _ kv IsInfinite (LitDouble x) = Just . mkBool kv $  isInfinite x
evalPrim1' _ _ _ _ = Nothing

evalPrim2 :: KnownValues -> Primitive -> Lit -> Lit -> Maybe Expr
evalPrim2 kv Ge x y = evalPrim2NumCharBool (>=) kv x y
evalPrim2 kv Gt x y = evalPrim2NumCharBool (>) kv x y
evalPrim2 kv Eq x y = evalPrim2NumCharBool (==) kv x y
evalPrim2 kv Neq x y = evalPrim2NumCharBool (/=) kv x y
evalPrim2 kv Lt x y = evalPrim2NumCharBool (<) kv x y
evalPrim2 kv Le x y = evalPrim2NumCharBool (<=) kv x y
evalPrim2 _ Plus x y = evalPrim2Num (+) x y
evalPrim2 _ Minus x y = evalPrim2Num (-) x y
evalPrim2 _ Mult x y = evalPrim2Num (*) x y
evalPrim2 _ Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ Quot x y = if isZero y then error "Have Quot _ 0" else evalPrim2Integral quot x y
evalPrim2 _ Rem x y = if isZero y then error "Have Rem _ 0" else evalPrim2Integral rem x y
evalPrim2 _ Mod x y = evalPrim2Integral mod x y

evalPrim2 kv FpGeq x y = evalPrim2NumCharBool (>=) kv x y
evalPrim2 kv FpGt x y = evalPrim2NumCharBool (>) kv x y
evalPrim2 kv FpEq x y = evalPrim2NumCharBool (==) kv x y
evalPrim2 kv FpLt x y = evalPrim2NumCharBool (<) kv x y
evalPrim2 kv FpLeq x y = evalPrim2NumCharBool (<=) kv x y
evalPrim2 _ FpAdd x y = evalPrim2Num (+) x y
evalPrim2 _ FpSub x y = evalPrim2Num (-) x y
evalPrim2 _ FpMul x y = evalPrim2Num (*) x y
evalPrim2 _ FpDiv x y = evalPrim2Fractional (/) x y

evalPrim2 kv StrGe x y = evalPrim2NumCharBool (>=) kv x y
evalPrim2 kv StrGt x y = evalPrim2NumCharBool (>) kv x y
evalPrim2 kv StrLt x y = evalPrim2NumCharBool (<) kv x y
evalPrim2 kv StrLe x y = evalPrim2NumCharBool (<=) kv x y

evalPrim2 _ RationalToFloat (LitInt x) (LitInt y) =
       Just . Lit . LitFloat $ fromIntegral x / fromIntegral y
evalPrim2 _ RationalToDouble (LitInt x) (LitInt y) =
       Just . Lit . LitDouble $ fromIntegral x / fromIntegral y

evalPrim2 _ _ _ _ = Nothing

evalTypeDCPrim2 :: TypeEnv -> Primitive -> Type -> DataCon -> Maybe Expr
evalTypeDCPrim2 tenv DataToTag t dc =
    case unTyApp t of
        TyCon n _:_ | Just adt <- M.lookup n tenv ->
            let
                dcs = dataCon adt
            in
            fmap (Lit . LitInt . fst) . L.find ((==) dc . snd) $ zip [1..] dcs
        _ -> error "evalTypeDCPrim2: Unsupported Primitive Op"
evalTypeDCPrim2 _ _ _ _ = Nothing

evalTypeLitPrim2 :: TypeEnv -> Primitive -> Type -> Integer -> Maybe Expr
evalTypeLitPrim2 tenv TagToEnum t i =
    case unTyApp t of
        TyCon n _:_ | Just adt <- M.lookup n tenv ->
            let
                dcs = dataCon adt
            in
            maybe (Just $ Prim Error TyBottom) (Just . Data)
                                        $ ith dcs (fromInteger i)
        _ -> error "evalTypeLitPrim2: Unsupported Primitive Op"
evalTypeLitPrim2 _ _ _ _ = Nothing

ith :: [a] -> Integer -> Maybe a
ith (x:_) 0 = Just x
ith (_:xs) n = assert (n > 0) ith xs (n - 1)
ith _ _ = Nothing

isZero :: Lit -> Bool
isZero (LitInt 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumCharBool :: (forall a . Ord a => a -> a -> Bool) -> KnownValues -> Lit -> Lit -> Maybe Expr
evalPrim2NumCharBool f kv (LitInt x) (LitInt y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitFloat x) (LitFloat y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitDouble x) (LitDouble y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitRational x) (LitRational y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitChar x) (LitChar y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool _ _ _ _ = Nothing

evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Num f (LitInt x) (LitInt y) = Just . Lit . LitInt $ f x y
evalPrim2Num f (LitFloat x) (LitFloat y) = Just . Lit . LitFloat $ f x y
evalPrim2Num f (LitDouble x) (LitDouble y) = Just . Lit . LitDouble $ f x y
evalPrim2Num f (LitRational x) (LitRational y) = Just . Lit . LitRational $ f x y
evalPrim2Num _ _ _ = Nothing

evalPrim2Fractional  :: (forall a . Fractional a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Fractional f (LitFloat x) (LitFloat y) = Just . Lit . LitFloat $ f x y
evalPrim2Fractional f (LitDouble x) (LitDouble y) = Just . Lit . LitDouble $ f x y
evalPrim2Fractional f (LitRational x) (LitRational y) = Just . Lit . LitRational $ f x y
evalPrim2Fractional _ _ _ = Nothing

evalPrim2Integral :: (forall a . Integral a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Integral f (LitInt x) (LitInt y) = Just . Lit . LitInt $ f x y
evalPrim2Integral _ _ _ = Nothing

evalPrim1Floating :: (forall a . Floating a => a -> a) -> Lit -> Maybe Expr
evalPrim1Floating f (LitFloat x) = Just . Lit . LitFloat $ f x
evalPrim1Floating f (LitDouble x)  = Just . Lit . LitDouble $ f x
evalPrim1Floating _ _ = Nothing

-- | Evaluate certain primitives applied to symbolic expressions, when possible
evalPrimSymbolic :: ExprEnv -> TypeEnv -> NameGen -> KnownValues -> Expr -> Maybe (Expr, ExprEnv, [PathCond], NameGen)
evalPrimSymbolic eenv tenv ng kv e
    | [Prim DataToTag _, type_t, cse] <- unApp e
    , Type t <- dig eenv type_t
    , Case v@(Var _) _ _ alts <- cse
    , TyCon tn _:_ <- unTyApp t
    , Just adt <- M.lookup tn tenv =
        let
            alt_p = map (\(Alt (LitAlt l) alt_e) ->
                            let
                                Data dc = appCenter alt_e
                            in
                            (l, dc)) alts

            dcs = dataCon adt
            num_dcs = zip (map (Lit . LitInt) [0..]) dcs

            (ret, ng') = freshId TyLitInt ng 

            new_pc = map (`ExtCond` True)
                   $ mapMaybe (\(alt_l, alt_dc) ->
                            fmap (\(nn, _) -> eq v (Lit alt_l) `eq` eq (Var ret) nn)
                        $ L.find ((==) alt_dc . snd) num_dcs) alt_p
        in
        Just (Var ret, E.insertSymbolic ret eenv, new_pc, ng')
    -- G2 uses actual Bools in primitive comparisons, whereas GHC uses 0# and 1#.
    -- We thus need special handling so that, in G2, we don't try to convert to Bool via a TagToEnum
    -- (which has type Int# -> a).  Instead, we simply return the Bool directly.
    | tBool <- tyBool kv
    , [Prim TagToEnum _, _, pe] <- unApp e
    , typeOf (dig eenv pe) == tBool = Just (pe, eenv, [], ng)
    | [Prim TagToEnum _, type_t, pe] <- unApp e
    , Type t <- dig eenv type_t =
        case unTyApp t of
            TyCon n _:_ | Just adt <- M.lookup n tenv ->
                let
                    (b, ng') = freshId TyLitInt ng 
                    dcs = dataCon adt
                    alts = zipWith (\l dc -> Alt (LitAlt (LitInt l)) (Data dc)) [0..] dcs
                    alt_d = Alt Default (Prim Error t)
                in
                Just (Case pe b t (alt_d:alts), E.insertSymbolic b eenv, [], ng')
            _ -> error "evalTypeLitPrim2: Unsupported Primitive Op"
    | otherwise = Nothing
    where
        eq e1 = App (App (mkEqPrimType (typeOf e1) kv) e1)

dig :: ExprEnv -> Expr -> Expr
dig eenv (Var (Id n _)) | Just (E.Conc e) <- E.lookupConcOrSym n eenv = dig eenv e
dig _ e = e