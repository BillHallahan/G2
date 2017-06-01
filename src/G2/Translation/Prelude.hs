module G2.Translation.Prelude where

import G2.Core.Language

-- | Types
--   Internally in Haskell we have:
--
--     data Int = I# Int#
--
--   In order to represent unwrapped types, we use:
--       Int#    -> TyRawInt
--       Float#  -> TyRawFloat
--       Double# -> TyRawDouble
--       Char#   -> TyRawChar
-- Int
p_ty_int = TyConApp "Int" []
p_d_int = DC ("I#", -1, p_ty_int, [TyRawInt])

-- Float
p_ty_float = TyConApp "Float" []
p_d_float = DC ("F#", -2, p_ty_float, [TyRawFloat])

-- Double
p_ty_double = TyConApp "Double" []
p_d_double = DC ("D#", -3, p_ty_double, [TyRawDouble])

-- Char
p_ty_char = TyConApp "Char" []
p_d_char = DC ("C#", -4, p_ty_char, [TyRawChar])

-- Bool  -- Throw this in for free!
p_ty_bool = TyConApp "Bool" []
p_d_true = DC ("True", -5, p_ty_bool, [])
p_d_false = DC ("False", -6, p_ty_bool, [])

prelude_t_decls = [ ("Int",    TyAlg "Int"    [p_d_int])
                  , ("Float",  TyAlg "Float"  [p_d_float])
                  , ("Double", TyAlg "Double" [p_d_double])
                  , ("Char",   TyAlg "Char"   [p_d_char])
                  , ("Bool",   TyAlg "Bool"   [p_d_true, p_d_false]) ]

-- | Operations
--   Expressions that are primitive and to our raw data types. These correspond
--   to stupid things like +# and *#, etc that are defined in terms of native
--   code we cannot look into.
o_add = ("+",  "Add")
o_sub = ("-",  "Sub")
o_mul = ("*",  "Mul")
o_eq  = ("==", "Eq")
o_ne  = ("/=", "Ne")
o_lt  = ("<",  "Lt")
o_le  = ("<=", "Le")
o_ge  = (">=", "Ge")
o_gt  = (">",  "Gt")

-- | Numerical Operators
e_num_ops = [ o_add, o_sub, o_mul
            , o_eq, o_ne
            , o_lt, o_le, o_ge, o_gt ]

-- | Character Operators
e_char_ops = [ o_eq, o_ne
             , o_lt, o_le, o_ge, o_gt ]

-- | Boolean Operators
e_bool_ops = [o_eq, o_ne]

-- | Modified / Flagged Numerical Operators
e_num_ops_mod = [(o ++ s, Const (COp ("p_e_" ++ n ++ s) (TyFun t (TyFun t t))))
                | (s, t) <- [ ("!I", p_ty_int)
                            , ("!F", p_ty_float)
                            , ("!D", p_ty_double) ],
                  (o, n) <- e_num_ops]

-- | Modified / Flagged Character Operators
e_char_ops_mod = map
    (\(o, n) -> (o ++ "!C", Const (COp ("p_e_" ++ n ++ "!C")
                               (TyFun p_ty_char (TyFun p_ty_char p_ty_char)))))
    e_char_ops

-- | Modified / Flagged Boolean Operators
e_bool_ops_mod = map 
    (\(o, n) -> (o ++ "!B", Const (COp ("p_e_" ++ n ++ "!B")
                               (TyFun p_ty_bool (TyFun p_ty_bool p_ty_bool)))))
    e_bool_ops

-- | Prelude Expression Environment
prelude_e_decls = e_num_ops_mod ++ e_char_ops_mod ++ e_bool_ops_mod

-- | Default Data Constructor
dc_default = DC ("DEFAULT", 0::Int, TyBottom, [])

op_eq = Var "==" TyBottom
d_eq  = Var "$dEq" TyBottom

