{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Execution.PrimitiveEval (evalPrims, mutVarTy, evalPrimWithState, newMutVar, maybeEvalPrim, evalPrimSymbolic) where

import G2.Execution.NewPC
import G2.Language.AST
import G2.Language.Expr
import qualified G2.Language.KnownValues as KV
import G2.Language.Naming
import G2.Language.Primitives
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing

import Control.Exception
import Data.Bits
import Data.Char
import Data.Foldable
import qualified Data.HashMap.Lazy as M
import qualified Data.List as L
import Data.Maybe
import qualified G2.Language.ExprEnv as E
import G2.Language.MutVarEnv

evalPrims :: ASTContainer m Expr => TypeEnv -> KnownValues -> m -> m
evalPrims tenv kv = modifyContainedASTs (evalPrims' tenv kv . simplifyCasts)

evalPrims' :: TypeEnv -> KnownValues -> Expr -> Expr
evalPrims' tenv kv a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim' tenv kv [p, evalPrims' tenv kv l]
        [p@(Prim _ _), l1, l2] ->
            evalPrim' tenv kv [p, evalPrims' tenv kv l1, evalPrims' tenv kv l2]
        [p@(Prim _ _), l1, l2, l3] ->
            evalPrim' tenv kv [p, evalPrims' tenv kv l1, evalPrims' tenv kv l2, evalPrims' tenv kv l3]
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

    | [Prim p _, x, y, z] <- xs = evalPrim3 kv p x y z

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
                  -> Maybe (NewPC t, NameGen) -- ^ `Just` if `e` is a primitive operation that this function reduces, `Nothing` otherwise
evalPrimWithState s@(State { known_values = kv, type_env = tenv, expr_env = eenv }) ng (App (Prim DecodeFloat _) e_arg) | e <- deepLookupExprPastTicks e_arg eenv =
    let

        -- The decodeFloat function returns a (signed and scaled) significand and exponent from a float.
        -- More details on scaling are in Note [Scaled decodeFloat], below.

        (ex_bits, sig_bits) = case typeOf e of
                                TyLitFloat -> (8, 23)
                                TyLitDouble -> (11, 52)
                                _ -> error "evalPrimWithState: decodeFloat - unsupported type"
        ty_ex = TyLitBV ex_bits
        ty_sig = TyLitBV sig_bits

        -- Introduce variables for the sign, exponent, and significant of the floating point number.
        -- Also introduces variables to account for shifting (see Note [Scaled decodeFloat])
        (sign, ng2) = freshSeededId (Name "sign" Nothing 0 Nothing) (TyLitBV 1) ng
        (ex, ng3) = freshSeededId (Name "exp" Nothing 0 Nothing) ty_ex ng2
        (sig, ng4) = freshSeededId (Name "sig" Nothing 0 Nothing) ty_sig ng3

        (shift_r_v, ng5) = freshSeededId (Name "shift_r" Nothing 0 Nothing) ty_sig ng4
        (shift_l_v, ng6) = freshSeededId (Name "shift_l" Nothing 0 Nothing) ty_sig ng5

        -- Setting up the Fp Primitive
        fp_exp = App (App (App (Prim Fp TyUnknown) (Var sign)) (Var ex)) (Var sig)
        fp_pc = ExtCond (App (App (Prim Eq TyUnknown) fp_exp) e) True

        eenv' = foldl' (flip E.insertSymbolic) (expr_env s) [sign, ex, sig, shift_r_v, shift_l_v]

        -- Note [Scaled decodeFloat]
        -- The output significand includes the hidden bit, which is 1 for a normal float and 0 for a denormalized float.
        -- Further, the significand bits are shifted (the significand is scaled) to make the greatest bit 1
        -- (unless the significand it entirely 0). This shifting is accounted for by descreasing the exponent appropriately-
        -- that is, if the significand is shifted N bits left, the exponent is descreased by N.

        ---------------------------------------------------------------------------------------------
        -- Shift value in G2
        ---------------------------------------------------------------------------------------------
        -- We need to move the first 1 in the bit string all the way to the left- however, SMT-LIB does
        -- not give any direct way to calculate the number of leading 0's.  So instead, we find the amount
        -- of shifting required to shift the first 1 all the way to the right (making the bit string just
        -- equal to 1) and then subtract that value from the full bitstring width.
        --
        -- If the significand is 0, the shift variable is not specified.
        --
        -- For example, suppose that the bit strings are of width 6, the exponent is b000000, and the significand
        -- is b000110.  We would then calculate that:
        --         shift_r_amount = 2  (since shifting b000110 to the right by 2 gives the bitstring b000001)
        --         shift_l_amount = 3  (since shifting b000110 to the left by 3 gives a bitstring with a leading 1, that is b110000)
        -- Note that
        --         shift_l_amount = width - shift_r_amount - 1
        -- When we account for the float's hidden bit, we actually then just want to shift the significand (width - shift_r_amount) to the left.

        is_zero = App (App (Prim Eq TyUnknown) (Var sig)) (Lit $ integerToBV sig_bits 0)
        -- Shift the significand to the right until equal to 1.
        shift_r_amount = mkApp
                            [ Prim Eq TyUnknown
                            , mkApp [Prim ShiftRBV TyUnknown, Var sig, Var shift_r_v]
                            , Lit $ integerToBV sig_bits 1 ]
        -- Calculate how far the first 1 is from the left.
        shift_l_amount = mkApp
                         [ Prim MinusBV TyUnknown
                         , Lit $ integerToBV sig_bits (toInteger sig_bits)
                         , Var shift_r_v ]
        shift_or = mkApp [ Prim Or TyUnknown
                         , is_zero
                         , App (App (Prim Eq TyUnknown) (Var shift_l_v)) shift_l_amount ]

        shift_pc1 = ExtCond shift_r_amount True
        shift_pc2 = ExtCond shift_or True

        ---------------------------------------------------------------------------------------------
        -- Exponent value in G2
        ---------------------------------------------------------------------------------------------
        -- If the exponent from the FP primitive is 0, float is denormalized and will be shifted according
        -- to Note [Scaled decodeFloat], so we have to compensate by adjusting the exponent returned by decodeFloat
        exp_int = App (Prim (BVToInt ex_bits) (TyFun ty_ex TyLitInt)) (Var ex)

        exp_e = mkApp [ Prim PIf TyUnknown
                      , App (App (Prim Eq TyUnknown) exp_int) (Lit (LitInt 0))
                      , mkApp [ Prim Minus TyUnknown
                              , exp_int
                              , mkApp [ Prim Minus TyUnknown
                                      , App (Prim (BVToInt sig_bits) (TyFun ty_ex TyLitInt)) (Var shift_l_v)
                                      , Lit (LitInt 1) ] ]
                      , exp_int ]
        ---------------------------------------------------------------------------------------------
        -- Significand value in G2
        ---------------------------------------------------------------------------------------------
        -- If the exponent from the FP primitive is 0, float is denormalized with a leading bit of 1,
        -- and we need to shift (see Note [Scaled decodedFloat]), otherwise leading bit is one
        ext_sig = mkApp [ Prim PIf TyUnknown
                        , App (App (Prim Eq TyUnknown) exp_int) (Lit (LitInt 0))
                        , mkApp [ Prim ConcatBV TyUnknown
                                , Lit $ LitBV [1]
                                , mkApp [ Prim ShiftLBV TyUnknown
                                        , Var sig
                                        , Var shift_l_v ]
                                ]
                        , mkApp [Prim ConcatBV TyUnknown, Lit $ LitBV [1], Var sig] ]
        unsign_sig = App (Prim (BVToInt (sig_bits + 1)) (TyFun ty_sig TyLitInt)) ext_sig
        -- Negate significand if needed
        sig_e = mkApp [ Prim PIf TyUnknown
                      , App (App (Prim Eq TyUnknown) (App (Prim (BVToInt 1) (TyFun (TyLitBV 1) TyLitInt)) (Var sign))) (Lit (LitInt 0))
                      , unsign_sig
                      , App (Prim Negate TyUnknown) unsign_sig]

        ---------------------------------------------------------------------------------------------
        -- Return value of decodeFloat, (# significand, exponent #)
        ---------------------------------------------------------------------------------------------
        curr' = App
                    (App 
                        (App 
                            (App 
                                (App (App (mkPrimTuple kv tenv) (Type TyUnknown)) (Type TyUnknown))
                                (Type ty_ex)
                            ) 
                            (Type ty_sig)
                        )
                        sig_e
                    ) 
                    exp_e
    in
    Just ( NewPC { state = s { expr_env = eenv'
                             , curr_expr = CurrExpr Return curr' }
                 , new_pcs = [ fp_pc, shift_pc1, shift_pc2 ]
                 , concretized = [] }
         , ng6)
evalPrimWithState s ng (App (Prim HandleGetPos _) hnd)
    | (Prim (Handle n) _) <- deepLookupExprPastTicks hnd (expr_env s)
    , Just (HandleInfo { h_pos = pos }) <- M.lookup n (handles s) =
        Just (newPCEmpty $ s { curr_expr = CurrExpr Evaluate (Var pos) }, ng)
evalPrimWithState s ng (App (App (Prim HandleSetPos _) (Var new_pos)) hnd)
    | (Prim (Handle n) _) <- deepLookupExprPastTicks hnd (expr_env s)
    , Just hi <- M.lookup n (handles s) =
        let
            s' = s { curr_expr = CurrExpr Evaluate (mkUnit (known_values s) (type_env s))
                   , handles = M.insert n (hi { h_pos = new_pos }) (handles s)}
        in
        Just (newPCEmpty $ s', ng)
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
        Just (newPCEmpty $ s', ng')
evalPrimWithState s ng (App (App (App (App (Prim NewMutVar _) (Type t)) (Type ts)) e) _) =
    let (s', ng') = newMutVar s ng MVConc ts t e in Just (newPCEmpty s', ng')
evalPrimWithState s ng (App (App (App (App (Prim ReadMutVar _) _) _) mv_e) _)
    | (Prim (MutVar mv) _) <- deepLookupExprPastTicks mv_e (expr_env s) =
    let
        i = lookupMvVal mv (mutvar_env s)
        s' = maybe (error "evalPrimWithState: MutVar not found")
                   (\i' -> s { curr_expr = CurrExpr Evaluate (Var i') })
                   i
    in
    Just (newPCEmpty s', ng)
evalPrimWithState s ng (App (App (App (App (App (Prim WriteMutVar _) _) (Type t)) mv_e) e) pr_s)
    | (Prim (MutVar mv) _) <- deepLookupExprPastTicks mv_e (expr_env s) =
    let
        (i, ng') = freshId t ng
        s' = s { expr_env = E.insert (idName i) e (expr_env s)
               , mutvar_env = updateMvVal mv i (mutvar_env s)
               , curr_expr = CurrExpr Evaluate pr_s }
    in
    Just (newPCEmpty s', ng')
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
evalPrim1 (BVToInt _) (LitBV bv) = Just . Lit . LitInt $ bvToInteger bv
evalPrim1 Chr (LitInt x) = Just . Lit $ LitChar (chr $ fromInteger x)
evalPrim1 OrdChar (LitChar x) = Just . Lit $ LitInt (toInteger $ ord x)
evalPrim1 WGenCat (LitInt x) = Just . Lit $ LitInt (toInteger . fromEnum . generalCategory . toEnum $ fromInteger x)
evalPrim1 _ _ = Nothing

evalPrim1' :: TypeEnv -> KnownValues -> Primitive -> Lit -> Maybe Expr
evalPrim1' tenv kv IntToString (LitInt x) =
    let
        char_dc = mkDCChar kv tenv
    in
    Just . mkG2List kv tenv TyLitChar . map (App char_dc . Lit . LitChar) $ show x
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
evalPrim2 kv Lt x y = evalPrim2NumCharBool (<) kv x y
evalPrim2 kv Le x y = evalPrim2NumCharBool (<=) kv x y
evalPrim2 _ Plus x y = evalPrim2Num (+) x y
evalPrim2 _ Minus x y = evalPrim2Num (-) x y
evalPrim2 _ Mult x y = evalPrim2Num (*) x y
evalPrim2 _ Div x y = if isZero y then error "Have Div _ 0" else evalPrim2Fractional (/) x y
evalPrim2 _ Quot x y = if isZero y then error "Have Quot _ 0" else evalPrim2Integral quot x y
evalPrim2 _ Rem x y = if isZero y then error "Have Rem _ 0" else evalPrim2Integral rem x y
evalPrim2 _ Mod x y = evalPrim2Integral mod x y

evalPrim2 _ ConcatBV (LitBV bv1) (LitBV bv2) = Just . Lit $ LitBV (bv1 ++ bv2)
evalPrim2 _ ShiftLBV (LitBV bv1) (LitBV bv2) =
    let shft = fromInteger $ bvToInteger bv2 in
    Just . Lit . LitBV $ drop shft bv1 ++ replicate shft 0
evalPrim2 _ ShiftRBV (LitBV bv1) (LitBV bv2) =
    let
        shft = fromInteger $ bvToInteger bv2
        bv1' = reverse . drop shft $ reverse bv1
    in
    Just . Lit . LitBV $ replicate shft 0 ++ bv1'

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

evalPrim3 :: KnownValues -> Primitive -> Expr -> Expr -> Expr -> Maybe Expr
evalPrim3 kv PIf (Data (DataCon { dc_name = b })) e1 e2 | b == KV.dcTrue kv = Just e1
                                                        | b == KV.dcFalse kv = Just e2
evalPrim3 _ p _ _ _ = Nothing

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