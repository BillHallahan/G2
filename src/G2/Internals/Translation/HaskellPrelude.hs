module G2.Internals.Translation.HaskellPrelude
    ( module G2.Internals.Translation.HaskellPrelude ) where

import G2.Internals.Core.Language

-- | Types
--   In G2 Core we use the following to represent primitive types:
--       TyRawInt    -> Int#
--       TyRawFloat  -> Float#
--       TyRawDouble -> Double#
--       TyRawChar   -> Char#
p_ty_int    = TyConApp "Int" []
p_d_int     = DataCon "I#" (-1) p_ty_int [TyRawInt]
p_ty_float  = TyConApp "Float" []
p_d_float   = DataCon "F#" (-2) p_ty_float [TyRawFloat]
p_ty_double = TyConApp "Double" []
p_d_double  = DataCon "D#" (-3) p_ty_double [TyRawDouble]
p_ty_char   = TyConApp "Char" []
p_d_char    = DataCon "C#" (-4) p_ty_char [TyRawChar]
p_ty_bool   = TyConApp "Bool" []
p_d_true    = DataCon "True" (-5) p_ty_bool []
p_d_false   = DataCon "False" (-6) p_ty_bool []

-- | Prelude Type Declarations
prelude_t_decls = [ ("Int",    TyAlg "Int"    [p_d_int])
                  , ("Float",  TyAlg "Float"  [p_d_float])
                  , ("Double", TyAlg "Double" [p_d_double])
                  , ("Char",   TyAlg "Char"   [p_d_char])
                  , ("Bool",   TyAlg "Bool"   [p_d_true, p_d_false]) ]

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


op_eq = Var "==" TyBottom
d_eq  = Var "$dEq" TyBottom

