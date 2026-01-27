{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}

module G2.Execution.PrimitiveEval ( evalPrimsSharing
                                  , evalPrims
                                  , mutVarTy
                                  , evalPrimWithState
                                  , newMutVar
                                  , maybeEvalPrim
                                  , evalPrimSymbolic
                                  
                                  , toString) where

import G2.Execution.NewPC
import G2.Execution.MutVar
import G2.Execution.SymToCase
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
import Data.Foldable
import qualified Data.HashMap.Lazy as M
import qualified Data.HashSet as HS
import qualified Data.List as L
import Data.Maybe
import qualified G2.Language.ExprEnv as E
import G2.Language.MutVarEnv
import qualified G2.Language.Stack as Stck
import qualified G2.Language.TyVarEnv as TV 

import GHC.Float
import G2.Language.ExprEnv (deepLookupVar)
import G2.Language.KnownValues (KnownValues(smtStringFuncs))
import G2.Language.TypeClasses.TypeClasses

-- | Evaluates primitives at the root of the passed `Expr` while updating the `ExprEnv`
-- to share computed results.
evalPrimsSharing :: ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> Expr -> (Expr, ExprEnv)
evalPrimsSharing eenv tenv tv_env kv tc e =
    let (_, e', eenv') = evalPrimsSharing' HS.empty eenv tenv tv_env kv tc . simplifyCasts tv_env $ e in (e', eenv')

-- | Passed back in evalPrimsSharing' to indicate whether a new value has been computed,
-- and thus indicate whether insertion into the `ExprEnv` is needed.
data NeedUpdate = Update | NoUpdate deriving Show

evalPrimsSharing' :: HS.HashSet Name -> ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> Expr -> (NeedUpdate, Expr, ExprEnv)
evalPrimsSharing' seen eenv tenv tv_env kv tc a@(App _ _) =
    case unApp a of
        p@(Prim _ _):es ->
            let
                (eenv', es') = L.mapAccumR
                                    (\eenv_ e -> let (_, e', eenv_') = evalPrimsSharing' seen eenv_ tenv tv_env kv tc e in (eenv_', e'))
                                    eenv $ map (inlineVarsForPrim eenv tc) es
                ev = evalPrim' eenv tenv tv_env kv tc (p:es')
            in
            (Update, ev, eenv')
        (Var (Id n _) ):xs | Just p@(Prim _ _) <- E.deepLookup n eenv -> evalPrimsSharing' seen eenv tenv tv_env kv tc (mkApp $ p:xs)
        _ -> (NoUpdate, a, eenv)
evalPrimsSharing' seen eenv tenv tv_env kv tc v@(Var (Id n _))
    | n `elem` seen = (NoUpdate, v, eenv)
    | otherwise =
        case E.lookupConcOrSym n eenv of
            Just (E.Conc e) -> case evalPrimsSharing' (HS.insert n seen) eenv tenv tv_env kv tc e of
                                    (Update, e', eenv') -> (Update, e', E.insert n e' eenv')
                                    r@(NoUpdate, _, _) -> r
            _ -> (NoUpdate, v, eenv)
evalPrimsSharing' _ eenv _ _ _ _ e = (NoUpdate, e, eenv)

inlineVarsForPrim :: ASTContainer c Expr => ExprEnv -> TypeClasses -> c -> c
inlineVarsForPrim eenv tc = modifyContainedASTs (inlineVarsForPrim' HS.empty eenv tc)

inlineVarsForPrim' :: HS.HashSet Name -> ExprEnv -> TypeClasses -> Expr -> Expr
inlineVarsForPrim' seen eenv tc (Var (Id n t))
    | not (n `HS.member` seen)
    , not (isTypeClass tc (returnType t))
    , Just (E.Conc e) <- E.lookupConcOrSym n eenv
    , not (isLam e) = inlineVarsForPrim' (HS.insert n seen) eenv tc e
inlineVarsForPrim' seen eenv tc e = modifyChildren (inlineVarsForPrim' seen eenv tc) e

evalPrims :: ASTContainer m Expr => ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> m -> m
evalPrims eenv tenv tv_env kv tc = modifyContainedASTs (evalPrims' eenv tenv tv_env kv tc . simplifyCasts tv_env)

evalPrims' :: ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> Expr -> Expr
evalPrims' eenv tenv tv_env kv tc a@(App x y) =
    case unApp a of
        [p@(Prim _ _), l] -> evalPrim' eenv tenv tv_env kv tc [p, evalPrims' eenv tenv tv_env kv tc l]
        [p@(Prim _ _), l1, l2] ->
            evalPrim' eenv tenv tv_env kv tc [p, evalPrims' eenv tenv tv_env kv tc l1, evalPrims' eenv tenv tv_env kv tc l2]
        [p@(Prim _ _), l1, l2, l3] ->
            evalPrim' eenv tenv tv_env kv tc [p, evalPrims' eenv tenv tv_env kv tc l1, evalPrims' eenv tenv tv_env kv tc l2, evalPrims' eenv tenv tv_env kv tc l3]
        _ -> App (evalPrims' eenv tenv tv_env kv tc x) (evalPrims' eenv tenv tv_env kv tc y)
evalPrims' eenv tenv tv_env kv tc e = modifyChildren (evalPrims' eenv tenv tv_env kv tc) e

evalPrim' :: ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> [Expr] -> Expr
evalPrim' eenv tenv tv_env kv tc xs = fromMaybe (mkApp xs) (maybeEvalPrim' eenv tenv tv_env kv tc xs)

maybeEvalPrim :: ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> Expr -> Maybe Expr
maybeEvalPrim eenv tenv tv_env kv tc = maybeEvalPrim' eenv tenv tv_env kv tc . unApp

maybeEvalPrim' :: ExprEnv -> TypeEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> [Expr] -> Maybe Expr
maybeEvalPrim' eenv tenv tv_env kv tc xs
    | [Prim p _, x] <- xs
    , Lit x' <- x
    , Just e <- evalPrim1 p x' = Just e
    | [Prim p _, x] <- xs
    , Lit x' <- x = evalPrim1' tenv kv p x'
    | [Prim p _, x] <- xs
    , Just e <- evalPrimADT1 kv p x = Just e

    | [Prim p _, x, y] <- xs
    , Lit x' <- x
    , Lit y' <- y = evalPrim2 kv p x' y'
    | [Prim p _, x, y] <- xs
    , Just e <- evalPrimADT2 kv tenv p x y = Just e

    | [Prim p _, x, y, z] <- xs
    , Just e <- evalPrimADT3 tenv kv p x y z = Just e

    | [Prim p _, x, y, z] <- xs = evalPrim3 kv p x y z

    | [Prim p _, Type t, x] <- xs
    , Just e <- evalTypeAnyArgPrim eenv tv_env kv tc p t x = Just e

    | [Prim p _, Type t, dc_e] <- xs, Data dc:_ <- unApp dc_e =
        evalTypeDCPrim2 tenv tv_env p t dc

    | [Prim p _, Type t, Lit (LitInt l)] <- xs =
        evalTypeLitPrim2 tenv p t l

    | otherwise = Nothing

-- | Evaluate primitives that need to read from or modify the State.
-- For more on MutVar's Note [MutVar Env] in G2.Language.MutVarEnv.
evalPrimWithState :: State t -- ^ Context to evaluate expression `e` in
                  -> NameGen
                  -> Expr -- ^ The expression `e` to evaluate
                  -> Maybe (NewPC t, NameGen) -- ^ `Just` if `e` is a primitive operation that this function reduces, `Nothing` otherwise
evalPrimWithState s@(State { known_values = kv, type_env = tenv, expr_env = eenv, tyvar_env = tvnv }) ng (App (Prim DecodeFloat _) e_arg) | e <- deepLookupExprPastTicks e_arg eenv =
    let

        -- The decodeFloat function returns a (signed and scaled) significand and exponent from a float.
        -- More details on scaling are in Note [Scaled decodeFloat], below.

        (ex_bits, sig_bits_1) = expSigBits (typeOf tvnv e)
        sig_bits = sig_bits_1 - 1
        ty_ex = TyLitBV ex_bits
        ty_sig = TyLitBV sig_bits

        -- Introduce variables for the sign, exponent, and significant of the floating point number.
        -- Also introduces variables to account for shifting (see Note [Scaled decodeFloat])
        (sign, ng2) = freshSeededId (Name "sign_fp" Nothing 0 Nothing) (TyLitBV 1) ng
        (ex, ng3) = freshSeededId (Name "exp_fp" Nothing 0 Nothing) ty_ex ng2
        (sig, ng4) = freshSeededId (Name "sig_fp" Nothing 0 Nothing) ty_sig ng3

        (exp_r, ng5) = freshSeededId (Name "exp" Nothing 0 Nothing) TyLitInt ng4
        (sig_r, ng6) = freshSeededId (Name "sig" Nothing 0 Nothing) TyLitInt ng5

        (shift_r_v, ng7) = freshSeededId (Name "shift_r" Nothing 0 Nothing) ty_sig ng6
        (shift_l_v, ng8) = freshSeededId (Name "shift_l" Nothing 0 Nothing) ty_sig ng7

        -- Setting up the Fp Primitive
        fp_exp = App (App (App (Prim Fp TyUnknown) (Var sign)) (Var ex)) (Var sig)
        fp_pc = ExtCond (App (App (Prim Eq TyUnknown) fp_exp) e) True

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
        shift_r_amount = mkApp [ Prim Or TyUnknown
                               , is_zero
                               , mkApp
                                    [ Prim Eq TyUnknown
                                    , mkApp [Prim ShiftRBV TyUnknown, Var sig, Var shift_r_v]
                                    , Lit $ integerToBV sig_bits 1 ]
                                ]
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
        exp_int = App (Prim BVToNat (TyFun ty_ex TyLitInt)) (Var ex)

        exp_e = mkApp [ Prim Ite TyUnknown
                      , App (App (Prim Eq TyUnknown) exp_int) (Lit (LitInt 0))
                      , mkApp [ Prim Minus TyUnknown
                              , exp_int
                              , mkApp [ Prim Minus TyUnknown
                                      , App (Prim BVToNat (TyFun ty_ex TyLitInt)) (Var shift_l_v)
                                      , Lit (LitInt 1) ] ]
                      , exp_int ]
        exp_pc = ExtCond (mkApp [Prim Eq TyUnknown, Var exp_r, exp_e]) True
        ---------------------------------------------------------------------------------------------
        -- Significand value in G2
        ---------------------------------------------------------------------------------------------
        -- If the exponent from the FP primitive is 0, float is denormalized with a leading bit of 1,
        -- and we need to shift (see Note [Scaled decodedFloat]), otherwise leading bit is one
        ext_sig = mkApp [ Prim Ite TyUnknown
                        , App (App (Prim Eq TyUnknown) exp_int) (Lit (LitInt 0))
                        , mkApp [ Prim ConcatBV TyUnknown
                                , Lit $ LitBV [1]
                                , mkApp [ Prim ShiftLBV TyUnknown
                                        , Var sig
                                        , Var shift_l_v ]
                                ]
                        , mkApp [Prim ConcatBV TyUnknown, Lit $ LitBV [1], Var sig] ]
        unsign_sig = App (Prim BVToNat (TyFun ty_sig TyLitInt)) ext_sig
        -- Negate significand if needed
        sig_e = mkApp [ Prim Ite TyUnknown
                      , App (App (Prim Eq TyUnknown) (App (Prim BVToNat (TyFun (TyLitBV 1) TyLitInt)) (Var sign))) (Lit (LitInt 0))
                      , unsign_sig
                      , App (Prim Negate TyUnknown) unsign_sig]
        sig_pc = ExtCond (mkApp [Prim Eq TyUnknown, Var sig_r, sig_e]) True

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
                        (Var sig_r)
                    ) 
                    (Var exp_r)
    in
    Just ( (SplitStatePieces 
             s
             [SD { new_conc_entries = []
                 , new_sym_entries = [sign, ex, sig, exp_r, sig_r, shift_r_v, shift_l_v]
                 , new_path_conds = [fp_pc, shift_pc1, shift_pc2, exp_pc, sig_pc]
                 , concretized = []
                 , new_true_assert = true_assert s
                 , new_assert_ids = assert_ids s
                 , new_curr_expr = CurrExpr Return curr'
                 , new_conc_types = []
                 , new_sym_types = []
                 , new_mut_vars = [] }
             ]), ng8
         )
evalPrimWithState s@(State { expr_env = eenv }) ng (App (App (Prim EncodeFloat t) m_arg) n_arg) =
    let
        -- `encodeFloat m n` returns one of the two closest representable floating-point numbers closest to m*b^^n, generally the closer,
        -- where b is the floating-point radix.
        --
        -- SMT-LIB does not have a floating-point exponentiation operator, but fortunately the radix for both Floats and Doubles is 2.
        -- For IEEE floating points, 2^n is represented by:
        --  (1) setting the exponent bits to the signed representation of (n + bias) and the significand to 0. (For exponents which fit in the exponent bits.)
        --  (2) setting the exponent field to all 0s, and having a single significand bit set to 1 (for powers of 2 representable as denormalized numbers.)

        rt = returnType t

        m = deepLookupExprPastTicks m_arg eenv
        n = deepLookupExprPastTicks n_arg eenv

        -- Size of the expected type
        (f_ex_bits, f_sig_bits_1) = expSigBits rt

        -- Sizes to work with during encoding.  We work with a larger size than we ultimately want to output to prevent overflow,
        -- then downcast before returning.
        w_ex_bits = f_ex_bits * 2
        w_sig_bits_1 = f_sig_bits_1 * 2
        w_sig_bits = w_sig_bits_1 - 1
        ty_ex = TyLitBV w_ex_bits

        (exp_bv, ng') = freshSeededId (Name "exp_bv" Nothing 0 Nothing) ty_ex ng
        (encoded_m_nan, ng'') = freshSeededId (Name "enc_nan" Nothing 0 Nothing) (TyLitFP w_ex_bits w_sig_bits_1) ng'
        (encoded, ng''') = freshSeededId (Name "enc" Nothing 0 Nothing) rt ng''

        offset = 2^(w_ex_bits - 1) - 1

        to_float = Prim (IntToFP w_ex_bits w_sig_bits_1) (TyFun TyLitInt rt)
        float_zero = mkApp [ Prim Fp TyUnknown
                           , Lit $ LitBV [0]
                           , Lit $ LitBV (replicate w_ex_bits 0)
                           , Lit $ LitBV (replicate w_sig_bits 0)]

        ---------------------------------------------------------------------------------------------
        -- Set up the float for 2^n.
        ---------------------------------------------------------------------------------------------
        sign_2n = Lit $ LitBV [0]

        -- If n > -offset, we can represent the required exponent as a normalized float
        scl_exp = mkApp [ Prim Plus (mkTyFun [TyLitInt, TyLitInt, TyLitInt])
                        , n
                        , Lit $ LitInt offset]
        exp_eq = mkApp [ Prim Eq TyUnknown
                       , scl_exp
                       , mkApp [ Prim (BVToNat ) (mkTyFun [TyLitBV w_ex_bits, TyLitInt])
                               , Var exp_bv ]
                       ]
        exp_pc = ExtCond exp_eq True

        sig_2n = Lit . LitBV $ replicate w_sig_bits 0

        -- If n <= -offset, the required exponent is a denormalized float
        de_exp = Lit . LitBV $ replicate w_ex_bits 0
        de_sig = mkApp [ Prim ShiftRBV TyUnknown
                       , Lit . LitBV $ 1:replicate (w_sig_bits - 1) 0
                       , mkApp [ Prim (IntToBV w_sig_bits) TyUnknown
                               , mkApp [ Prim Abs TyUnknown
                                       , mkApp [ Prim Plus TyUnknown
                                               , n
                                               , Lit . LitInt $ offset]
                                       ]
                               ]
                       ]

        n_fp = mkApp [ Prim Ite TyUnknown
                     , mkApp [ Prim Le TyUnknown, n, Lit $ LitInt (-offset)]
                     , App (App (App (Prim Fp TyUnknown) sign_2n) de_exp) de_sig -- Denormalized
                     , App (App (App (Prim Fp TyUnknown) sign_2n) (Var exp_bv)) sig_2n -- Normalized
                     ]

        ---------------------------------------------------------------------------------------------
        -- Multiply m*b^^n, adjust for NaN values (should be 0 based on observed behavior of encodeFloat primitive)
        ---------------------------------------------------------------------------------------------
        m_fp = mkApp [ to_float, m]

        mult_expr = mkApp [ Prim FpMul TyUnknown
                          , m_fp
                          , n_fp ]
        enc_m_nan_expr = mkApp [ Prim Eq TyUnknown
                               , Var encoded_m_nan
                               , mult_expr]
        enc_sel = mkApp [ Prim Ite TyUnknown
                        , mkApp [ Prim IsNaN TyUnknown
                                , Var encoded_m_nan
                                ]
                        , float_zero
                        , Var encoded_m_nan
                        ]
        enc_expr = mkApp [ Prim Eq TyUnknown
                         , Var encoded
                         , mkApp [ Prim (FPToFP f_ex_bits f_sig_bits_1) TyUnknown, enc_sel ]
                         ]

        curr' = Var encoded
    in
    Just ( (SplitStatePieces 
             s
             [SD { new_conc_entries = []
                 , new_sym_entries = [encoded, encoded_m_nan, exp_bv]
                 , new_path_conds = [exp_pc, ExtCond enc_m_nan_expr True, ExtCond enc_expr True]
                 , concretized = []
                 , new_true_assert = true_assert s
                 , new_assert_ids = assert_ids s
                 , new_curr_expr = CurrExpr Return curr'
                 , new_conc_types = []
                 , new_sym_types = []
                 , new_mut_vars = [] }
             ]), ng'''
         )
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
            ty_string = typeOf (tyvar_env s) pos

            (new_pos, ng') = freshSeededId (Name "pos" Nothing 0 Nothing) ty_string ng
            e = mkApp [mkCons (known_values s) (type_env s), Type ty_string, c, Var new_pos]
            s' = s { expr_env = E.insert (idName pos) e 
                              $ E.insertSymbolic new_pos (expr_env s)
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
evalPrimWithState s ng (App (Prim Raise _) e2) = Just (
                                                   (newPCEmpty $ s { curr_expr = CurrExpr Evaluate (App (Prim Error TyBottom) e2)
                                                                   , error_raised = True })
                                                   , ng)
evalPrimWithState s ng (App (App (Prim Catch _) run) hand) = Just (
                                                   (newPCEmpty $ s { curr_expr = CurrExpr Evaluate run
                                                                   , exec_stack = Stck.push (CatchFrame hand) (exec_stack s)
                                                                   })
                                                   , ng)

evalPrimWithState _ _ _ = Nothing

deepLookupExprPastTicks :: Expr -> ExprEnv -> Expr
deepLookupExprPastTicks (Var i@(Id n _)) eenv =
    case E.lookupConcOrSym n eenv of
        Just (E.Conc e) -> deepLookupExprPastTicks e eenv
        _ -> Var i
deepLookupExprPastTicks (Tick _ e) eenv = deepLookupExprPastTicks e eenv
deepLookupExprPastTicks e _ = e

expSigBits :: Type -> (Int, Int)
expSigBits (TyLitFP e s) =  (e, s)
expSigBits _ = error "evalPrimWithState: decodeFloat - unsupported type"

evalPrim1 :: Primitive -> Lit -> Maybe Expr
evalPrim1 Negate (LitInt x) = Just . Lit $ LitInt (-x)
evalPrim1 Negate (LitWord x) = Just . Lit $ LitWord (-x)
evalPrim1 Negate (LitRational x) = Just . Lit $ LitRational (-x)
evalPrim1 FpNeg (LitFloat x) = Just . Lit $ LitFloat (-x)
evalPrim1 FpNeg (LitDouble x) = Just . Lit $ LitDouble (-x)
evalPrim1 Abs (LitInt x) = Just . Lit $ LitInt (abs x)
evalPrim1 Abs (LitWord x) = Just . Lit $ LitWord (abs x)
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
evalPrim1 FloatToDouble (LitFloat x) = Just . Lit $ LitDouble (float2Double x)
evalPrim1 DoubleToFloat (LitDouble x) = Just . Lit $ LitFloat (double2Float x)
evalPrim1 (BVToInt _) (LitBV bv) = Just . Lit . LitInt $ bvToInteger bv
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

evalPrimADT1 :: KnownValues -> Primitive -> Expr -> Maybe Expr
evalPrimADT1 kv StrLen e = fmap (Lit . LitInt) (compLen e)
    where
        -- [] @Char
        compLen (App (Data dc) _ {- type -}) = assert (KV.dcEmpty kv == dcName dc) Just 0
        -- (:) @Char head tail
        compLen (App (App (App (Data dc) _ {- type -}) _ {- char -}) xs) = assert (KV.dcCons kv == dcName dc) fmap (+ 1) (compLen xs)
        compLen _ = Nothing

evalPrimADT1 _ _ _ = Nothing

evalPrimADT2 :: KnownValues -> TypeEnv -> Primitive -> Expr -> Expr -> Maybe Expr
evalPrimADT2 kv _ And e1 e2
    | Just b1 <- toBool kv e1
    , Just b2 <- toBool kv e2 = Just $ mkBool kv (b1 && b2)
evalPrimADT2 kv _ Or e1 e2
    | Just b1 <- toBool kv e1
    , Just b2 <- toBool kv e2 = Just $ mkBool kv (b1 || b2)

evalPrimADT2 kv tenv StrAppend xs ys = do
    t <- listType xs
    xs' <- toExprList xs
    ys' <- toExprList ys
    return . toListExpr kv tenv t $ xs' ++ ys'

evalPrimADT2 kv tenv StrAt xs (Lit (LitInt i)) = do
    xs' <- toString xs
    let c = if fromInteger i < length xs' then  [xs' !! (fromInteger i)] else []
    return $ toStringExpr kv tenv c

evalPrimADT2 kv _ StrPrefixOf pre s = do
    pre' <- toExprList pre
    s' <- toExprList s
    return . mkBool kv $ pre' `L.isPrefixOf` s'

evalPrimADT2 kv _ StrSuffixOf suf s = do
    suf' <- toExprList suf
    s' <- toExprList s
    return . mkBool kv $ suf' `L.isSuffixOf` s'

evalPrimADT2 kv _ Eq f s = fmap (mkBool kv) $ lstEq f s
    where
        -- List equality, currently used for strings and assumes types can be compared
        lstEq (App (App (App (Data dc_f) _) elem_f@(Lit _)) xs) (App (App (App (Data dc_s) _) elem_s@(Lit _)) ys) = do
            nxt <- lstEq xs ys
            assert (KV.dcCons kv == dcName dc_f && KV.dcCons kv == dcName dc_s) (Just (nxt && elem_f == elem_s))
        lstEq (App (App (App (Data _) _) _) _) (App (Data _) _) = Just False
        lstEq (App (Data _) _) (App (App (App (Data _) _) _) _) = Just False
        lstEq (App (Data dc_f) _) (App (Data dc_s) _) = assert (KV.dcEmpty kv == dcName dc_f && KV.dcEmpty kv == dcName dc_s) (Just True)
        lstEq _ _ = Nothing
evalPrimADT2 kv _ StrLe f s = fmap (mkBool kv) $ lstLe f s
    where
        lstLe (App (App (App (Data dc_f) _) (App _ (Lit (LitChar c1)))) xs) (App (App (App (Data dc_s) _) (App _ (Lit (LitChar c2)))) ys)
            | c1 <= c2 = Just True
            | c1 > c2 = Just False
            | otherwise = assert (KV.dcCons kv == dcName dc_f && KV.dcCons kv == dcName dc_s) lstLe xs ys
        lstLe (App (App (App (Data _) _) _) _) (App (Data _) _) = Just False
        lstLe (App (Data _) _) (App (App (App (Data _) _) _) _) = Just True
        lstLe (App (Data dc_f) _) (App (Data dc_s) _) = assert (KV.dcEmpty kv == dcName dc_f && KV.dcEmpty kv == dcName dc_s) (Just True)
        lstLe _ _= Nothing
evalPrimADT2 kv _ StrLt f s = do
    f' <- toString f
    s' <- toString s
    return $ mkBool kv (f' < s')
evalPrimADT2 kv _ StrGt f s = do
    f' <- toString f
    s' <- toString s
    return $ mkBool kv (f' > s')
evalPrimADT2 kv _ StrGe f s = do
    f' <- toString f
    s' <- toString s
    return $ mkBool kv (f' >= s')

evalPrimADT2 _ _ _ _ _ = Nothing

evalPrimADT3 :: TypeEnv -> KnownValues -> Primitive -> Expr -> Expr -> Expr -> Maybe Expr
evalPrimADT3 tenv kv StrSubstr str (Lit (LitInt s)) (Lit (LitInt e)) = substr str s e
    where
        -- Find a substring starting at index s and ending at index e - 1
        substr expr@(App (Data _) _) _ _ = Just expr
        substr (App (App (App (Data _) typ) _) _) 0 0 = Just (App (mkEmpty kv tenv) typ)
        substr (App (App (App (Data dc) typ) char) xs) 0 en = do
            next_substr <- substr xs 0 (en - 1)
            return (App (App (App (Data dc) typ) char) next_substr)
        substr (App (App (App (Data _) _) _) xs) st en = substr xs (st - 1) en
        substr _ _ _ = Nothing

evalPrimADT3 tenv kv StrReplace s orig rep = do
        t <- listType orig
        s' <- toExprList s
        orig' <- toExprList orig
        rep' <- toExprList rep
        return $ toListExpr kv tenv t (replace s' orig' rep')
    where
        replace [] _ _ = []
        replace xss@(x:xs) o r | Just xss' <- L.stripPrefix o xss = r ++ xss'
                               | otherwise = x:replace xs o r

evalPrimADT3 _ _ _ _ _ _ = Nothing

listType :: Expr -> Maybe Type
listType (App (Data _) (Type t)) = Just t
listType (App (App (App (Data _) (Type t)) _) _) = Just t
listType _ = Nothing

toString :: Expr -> Maybe String
toString (App (Data _) _) = Just []
toString (App (App (App (Data _) _) (App _ (Lit (LitChar c)))) xs) = fmap (c:) $ toString xs
toString _ = Nothing

toExprList :: Expr -> Maybe [Expr]
toExprList (App (Data _) _) = Just []
toExprList (App (App (App (Data _) _) l) xs) = fmap (l:) $ toExprList xs
toExprList _ = Nothing

toStringExpr :: KnownValues -> TypeEnv -> String -> Expr
toStringExpr kv tenv =
    let cons = mkCons kv tenv in
    foldr (\h t -> mkApp [ cons
                         , Type (tyChar kv)
                         , App (mkDCChar kv tenv) (Lit (LitChar h))
                         , t]) (App (mkEmpty kv tenv) (Type (tyChar kv)))

toListExpr :: KnownValues -> TypeEnv -> Type -> [Expr] -> Expr
toListExpr kv tenv t =
    let cons = mkCons kv tenv in
    foldr (\h tl -> mkApp [ cons
                          , Type t
                          , h
                          , tl]) (App (mkEmpty kv tenv) (Type t))

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

evalTypeAnyArgPrim :: ExprEnv -> TV.TyVarEnv -> KnownValues -> TypeClasses -> Primitive -> Type -> Expr -> Maybe Expr
evalTypeAnyArgPrim _ tv kv _ (TypeIndex tyh) t _ | tyh_strings tyh
                                                 , tyVarSubst tv t == tyString kv = Just (Lit (LitInt 1))
                                                 | tyh_prim_lists tyh
                                                 , TyApp t_list t_a <- tyVarSubst tv t
                                                 , t_list == tyList kv
                                                 ,  t_a == tyInt kv
                                                 || t_a == tyInteger kv
                                                 || t_a == tyFloat kv
                                                 || t_a == tyDouble kv = Just (Lit (LitInt 2 ))
                                                 | otherwise = Just (Lit (LitInt 0))
evalTypeAnyArgPrim eenv _ kv _ IsSMTRep _ e = Just . mkBool kv $ isSMTRep eenv kv e
evalTypeAnyArgPrim eenv _ kv tc EvalsToSMTRep _ e = Just . mkBool kv $ evalsToSMTRep HS.empty eenv kv tc e
evalTypeAnyArgPrim _ _ _ _ _ _ _ = Nothing

isSMTRep :: ExprEnv -> KnownValues -> Expr -> Bool
isSMTRep eenv kv e
    | Just (E.Sym _) <- c_s = True
    | Just (E.Conc e) <- c_s
    , Prim p _:_ <- unApp e
    , not (isErrorPrim p) = True
    | Just (E.Conc e) <- c_s 
    , isSymString eenv kv e = True
    | otherwise = False
    where
        c_s = case e of
                Var (Id n _) -> E.deepLookupConcOrSym n eenv
                _ -> Just (E.Conc e)

evalsToSMTRep :: HS.HashSet Name -> ExprEnv -> KnownValues -> TypeClasses -> Expr -> Bool
evalsToSMTRep seen eenv kv tc = go
    where
        go (Var (Id n t))
            | n `elem` smtStringFuncs kv = True
            | E.isSymbolic n eenv = True
            | isTypeClass tc (returnType t) = True
            | n `elem` seen = False
            | Just e' <- E.lookup n eenv = evalsToSMTRep (HS.insert n seen) eenv kv tc e'
        go (Let binds e) =
            let eenv' = foldr E.insertSymbolic eenv $ map fst binds in
            all (evalsToSMTRep seen eenv' kv tc . snd) binds && evalsToSMTRep seen eenv' kv tc e
        go (Case e _ _ alts) = go e && all altEvals alts
            where
                altEvals (Alt (DataAlt _ is) ae) = evalsToSMTRep seen (foldr E.insertSymbolic eenv is) kv tc ae
                altEvals (Alt _ ae) = go ae
        go (Data _) = True
        go (Lit _) = True
        go (App e1 e2) = go e1 && go e2
        go (Type _) = True
        go e | isSMTRep eenv kv e = True
        go _ = False

-- | Is the expression a symbolically representable string?
isSymString :: ExprEnv -> KnownValues ->  Expr -> Bool
isSymString eenv kv = go HS.empty
    where
        go seen (Var (Id n _))
            -- If we have already seen a variable, we have an infinite list, i.e.:
            -- @ xs = x:xs @
            -- this will cause problems for the SMT solver, so reject
            | HS.member n seen = False
            | Just (E.Sym _) <- E.deepLookupConcOrSym n eenv = True
            | Just (E.Conc e) <- E.deepLookupConcOrSym n eenv = go (HS.insert n seen) e
        go _ (Data dc) | dc_name dc == KV.dcCons kv = True
                       | dc_name dc == KV.dcEmpty kv = True
                       | dc_name dc == KV.dcChar kv = True
        go seen (App e1 e2)
            | Data _:_ <- unApp e1 = go seen e1 && go seen e2
        go _ (Lit (LitChar _)) = True
        go _ (Type _) = True
        go seen (Tick _ e) = go seen e
        go _ _ = False

evalTypeDCPrim2 :: TypeEnv -> TV.TyVarEnv -> Primitive -> Type -> DataCon -> Maybe Expr
evalTypeDCPrim2 tenv tv_env DataToTag t dc  =
    case unTyApp $ tyVarSubst tv_env t of
        TyCon n _:_ | Just adt <- M.lookup n tenv ->
            let
                dcs = dataCon adt
                dc_names = map dc_name dcs
            in
                fmap (Lit . LitInt . fst) . L.find ((==) (dc_name dc) . snd) $ zip [0..] dc_names
        _ -> error "evalTypeDCPrim2: Unsupported Primitive Op"
evalTypeDCPrim2 _ _ _ _ _ = Nothing

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
isZero (LitWord 0) = True
isZero (LitFloat 0) = True
isZero (LitDouble 0) = True
isZero _ = False

evalPrim2NumCharBool :: (forall a . Ord a => a -> a -> Bool) -> KnownValues -> Lit -> Lit -> Maybe Expr
evalPrim2NumCharBool f kv (LitInt x) (LitInt y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitWord x) (LitWord y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitFloat x) (LitFloat y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitDouble x) (LitDouble y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitRational x) (LitRational y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool f kv (LitChar x) (LitChar y) = Just . mkBool kv $ f x y
evalPrim2NumCharBool _ _ _ _ = Nothing

evalPrim2Num  :: (forall a . Num a => a -> a -> a) -> Lit -> Lit -> Maybe Expr
evalPrim2Num f (LitInt x) (LitInt y) = Just . Lit . LitInt $ f x y
evalPrim2Num f (LitWord x) (LitWord y) = Just . Lit . LitWord $ f x y
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
evalPrim2Integral f (LitWord x) (LitWord y) = Just . Lit . LitWord $ f x y
evalPrim2Integral _ _ _ = Nothing

evalPrim1Floating :: (forall a . Floating a => a -> a) -> Lit -> Maybe Expr
evalPrim1Floating f (LitFloat x) = Just . Lit . LitFloat $ f x
evalPrim1Floating f (LitDouble x)  = Just . Lit . LitDouble $ f x
evalPrim1Floating _ _ = Nothing

evalPrim3 :: KnownValues -> Primitive -> Expr -> Expr -> Expr -> Maybe Expr
evalPrim3 kv Ite (Data (DataCon { dc_name = b })) e1 e2 | b == KV.dcTrue kv = Just e1
                                                        | b == KV.dcFalse kv = Just e2
evalPrim3 _ _ _ _ _ = Nothing

-- | Evaluate certain primitives applied to symbolic expressions, when possible
evalPrimSymbolic ::  TV.TyVarEnv -> ExprEnv -> TypeEnv -> NameGen -> KnownValues -> Expr -> Maybe (Expr, ExprEnv, [PathCond], NameGen)
evalPrimSymbolic tv eenv tenv ng kv e
    | [Prim DataToTag _, type_t, (Var (Id n _))] <- unApp e
    , Just t <- TV.deepLookup tv type_t
    , Just sym_n <- deepLookupVar n eenv
    , E.isSymbolic sym_n eenv
    , TyCon tn _:_ <- unTyApp t
    , Just adt <- M.lookup tn tenv =
        let
            (_, bi) = fromJust $ getCastedAlgDataTy t tenv

            dcs = dataCon adt
            num_dcs = zip (map (Lit . LitInt) [0..]) dcs

            (cvar, ng') = freshId t ng

            (ret, cse, assume_pc, ng'', concs, syms) = createCaseExpr tv bi Nothing cvar t kv tenv ng' dcs

            eenv' = E.insertSymbolic ret . E.insert sym_n cse . E.insertExprs concs
                        $ L.foldl' (flip E.insertSymbolic) eenv syms
        in
        Just (Var ret, eenv', assume_pc, ng'')
    | [Prim DataToTag _, type_t, cse] <- unApp e
    , Just t <- TV.deepLookup tv type_t
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
    , typeOf tv (dig eenv pe) == tBool = Just (pe, eenv, [], ng)
    | [Prim TagToEnum _, type_t, pe] <- unApp e
    , Just t <- TV.deepLookup tv type_t =
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
        eq e1 = App (App (mkEqPrimType (typeOf tv e1) kv) e1)

dig :: ExprEnv -> Expr -> Expr
dig eenv (Var (Id n _)) | Just (E.Conc e) <- E.lookupConcOrSym n eenv = dig eenv e
dig _ e = e
