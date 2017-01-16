module G2.Sample.Prog1 where

import G2.Core.Language
import G2.Core.Prelude

import qualified Data.Map as M

t_decls = []

a = App (DCon p_d_int) (Const (CInt 123))
b = App (DCon p_d_int) (Const (CInt 456))

test1 = Case (Var "a" p_ty_int)
          [((p_d_int, ["a"])
            ,Case (Var "b" p_ty_int)
                  [((p_d_int, ["b"])
                    ,App (DCon p_d_int) (Var "a" TyInt))]
                  (TyConApp "Int" []))]
          (TyConApp "Int" [])

e_decls = [("a", a)
          ,("b", b)
          ,("test", test1)]

