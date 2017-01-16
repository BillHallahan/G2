module G2.Core.Prelude where

import G2.Core.Language

-- Some custom stuff for handling datatypes and primitives.

-- In Core2, the tyInt, tyReal, tyChar, and tyBool represent PRIMITIVEs that
-- we then need to wrap around in ADTs (like the way GHC) does if we want to
-- perform pattern matching on them, as our Core language definition only
-- permits matching on data constructors.

-- Internally GHC uses #, but we use ! here to more smoothly go into SMT land.

-- Int
p_ty_int = TyConApp "Int" []
p_d_int = ("Int!", -1, p_ty_int, [TyInt])

-- Float
p_ty_float = TyConApp "Float" []
p_d_float = ("Float!", -2, p_ty_float, [TyReal])

-- Double
p_ty_double = TyConApp "Double" []
p_d_double = ("Double!", -3, p_ty_double, [TyReal])

-- Char
p_ty_char = TyConApp "Char" []
p_d_char = ("Char!", -4, p_ty_char, [TyChar])

-- Bool
p_ty_bool = TyConApp "Bool" []
p_d_true = ("True", -5, p_ty_bool, [])
p_d_false = ("False", -6, p_ty_bool, [])

prelude_decls = [("Int",    TyAlg "Int" [p_d_int])
                ,("Float",  TyAlg "Float" [p_d_float])
                ,("Double", TyAlg "Double" [p_d_double])
                ,("Char",   TyAlg "Char" [p_d_char])
                ,("Bool",   TyAlg "Bool" [p_d_true, p_d_false])]

