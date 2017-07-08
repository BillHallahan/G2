module G2.Internals.Translation.HaskellPrelude
    ( module G2.Internals.Translation.HaskellPrelude ) where

import G2.Internals.Core.Language

-- | Types
--   In G2 Core we use the following to represent primitive types:
--       TyRawInt    -> Int#
--       TyRawFloat  -> Float#
--       TyRawDouble -> Double#
--       TyRawChar   -> Char#
p_ty_int    = TyConApp ("Int", 0 :: Int) []
p_d_int     = DataCon ("I#", 0 :: Int)  ((-1) :: Int) p_ty_int [TyRawInt]

p_ty_float  = TyConApp ("Float", 0 :: Int) []
p_d_float   = DataCon ("F#", 0 :: Int) ((-2) :: Int) p_ty_float [TyRawFloat]

p_ty_double = TyConApp ("Double", 0 :: Int) []
p_d_double  = DataCon ("D#", 0 :: Int) ((-3) :: Int) p_ty_double [TyRawDouble]
p_ty_char   = TyConApp ("Char", 0 :: Int) []
p_d_char    = DataCon ("C#", 0 :: Int) ((-4) :: Int) p_ty_char [TyRawChar]
p_ty_bool   = TyConApp ("Bool", 0 :: Int) []
p_d_true    = DataCon ("True", 0 :: Int) ((-5) :: Int) p_ty_bool []
p_d_false   = DataCon ("False", 0 :: Int) ((-6) :: Int) p_ty_bool []

-- | Prelude Type Declarations
prelude_t_decls = [ (("Int", 0),    TyAlg ("Int", 0 :: Int)    [p_d_int])
                  , (("Float", 0),  TyAlg ("Float", 0 :: Int)  [p_d_float])
                  , (("Double", 0), TyAlg ("Double", 0 :: Int) [p_d_double])
                  , (("Char", 0),   TyAlg ("Char", 0 :: Int)   [p_d_char])
                  , (("Bool", 0),   TyAlg ("Bool", 0 :: Int)   [p_d_true, p_d_false]) ]

-- | Expressions
o_add = ("+",  "Add")
o_sub = ("-",  "Sub")
o_mul = ("*",  "Mul")
o_eq  = ("==", "Eq")
o_ne  = ("/=", "Ne")
o_lt  = ("<",  "Lt")
o_le  = ("<=", "Le")
o_ge  = (">=", "Ge")
o_gt  = (">",  "Gt")

e_num_ops_raw = [ o_add, o_sub, o_mul
                , o_eq, o_ne
                , o_lt, o_le, o_ge, o_gt ]

e_char_ops_raw = [ o_eq, o_ne
                 , o_lt, o_le, o_ge, o_gt ]

e_bool_ops = [o_eq, o_ne]


op_eq = Var ("==", 0 :: Int) TyBottom
d_eq  = Var ("$dEq", 0 :: Int) TyBottom

