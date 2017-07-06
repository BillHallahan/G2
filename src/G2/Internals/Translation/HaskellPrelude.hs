module G2.Internals.Translation.HaskellPrelude
    ( module G2.Internals.Translation.HaskellPrelude ) where

import G2.Internals.Core.Language

-- | Types
--   In G2 Core we use the following to represent primitive types:
--       TyRawInt    -> Int#
--       TyRawFloat  -> Float#
--       TyRawDouble -> Double#
--       TyRawChar   -> Char#
p_ty_int    = TyConApp (Name "Int" 0) []
p_d_int     = DataCon (Name "I#" 0) (-1) p_ty_int [TyRawInt]
p_ty_float  = TyConApp (Name "Float" 0) []
p_d_float   = DataCon (Name "F#" 0) (-2) p_ty_float [TyRawFloat]
p_ty_double = TyConApp (Name "Double" 0) []
p_d_double  = DataCon (Name "D#" 0) (-3) p_ty_double [TyRawDouble]
p_ty_char   = TyConApp (Name "Char" 0) []
p_d_char    = DataCon (Name "C#" 0) (-4) p_ty_char [TyRawChar]
p_ty_bool   = TyConApp (Name "Bool" 0) []
p_d_true    = DataCon (Name "True" 0) (-5) p_ty_bool []
p_d_false   = DataCon (Name "False" 0) (-6) p_ty_bool []

-- | Prelude Type Declarations
prelude_t_decls = [ ("Int",    TyAlg (Name "Int" 0)    [p_d_int])
                  , ("Float",  TyAlg (Name "Float" 0)  [p_d_float])
                  , ("Double", TyAlg (Name "Double" 0) [p_d_double])
                  , ("Char",   TyAlg (Name "Char" 0)   [p_d_char])
                  , ("Bool",   TyAlg (Name "Bool" 0)   [p_d_true, p_d_false]) ]

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

e_num_ops_mod = [(o ++ s,Const (COp (Name ("p_e_" ++ n ++ s) 0) (TyFun t (TyFun t t)))) |
                     (s, t) <- [ ("!I", p_ty_int)
                               , ("!F", p_ty_float)
                               , ("!D", p_ty_double) ],
                     (o, n) <- e_num_ops_raw]

e_char_ops_mod = map
    (\(o, n) -> ( o ++ "!C"
                , Const (COp (Name ("p_e_" ++ n ++ "!C") 0)
                             (TyFun p_ty_char (TyFun p_ty_char p_ty_char)))))
    e_char_ops_raw

e_bool_ops_mod = map 
    (\(o, n) -> ( o ++ "!B"
                , Const (COp (Name ("p_e_" ++ n ++ "!B") 0)
                             (TyFun p_ty_bool (TyFun p_ty_bool p_ty_bool)))))
    e_bool_ops

-- | Prelude Expression Declarations
prelude_e_decls = e_num_ops_mod ++ e_char_ops_mod ++ e_bool_ops_mod

op_eq = Var (Name "==" 0) TyBottom
d_eq  = Var (Name "$dEq" 0) TyBottom

