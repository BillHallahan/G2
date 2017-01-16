fromList [("Bool",TyAlg "Bool" [("True",-5,TyConApp "Bool" [],[]),("False",-6,TyConApp "Bool" [],[])]),("Char",TyAlg "Char" [("Char!",-4,TyConApp "Char" [],[TyChar])]),("Double",TyAlg "Double" [("Double!",-3,TyConApp "Double" [],[TyReal])]),("Float",TyAlg "Float" [("Float!",-2,TyConApp "Float" [],[TyReal])]),("Int",TyAlg "Int" [("Int!",-1,TyConApp "Int" [],[TyInt])])]
fromList [("a",App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 123) TyInt)),("b",App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 456) TyInt)),("test1",Case (Var "a" (TyConApp "Int" [])) [((("Int!",-1,TyConApp "Int" [],[TyInt]),["a"]),Case (Var "b" (TyConApp "Int" [])) [((("Int!",-1,TyConApp "Int" [],[TyInt]),["b"]),App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Var "a" TyInt))] (TyConApp "Int" []))] (TyConApp "Int" []))]

>>> Case (Var "a" (TyConApp "Int" []))
         [((("Int!",-1,TyConApp "Int" [],[TyInt]),["a"])
          ,Case (Var "b" (TyConApp "Int" []))
                [((("Int!",-1,TyConApp "Int" [],[TyInt]),["b"])
                 >>> ,App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Var "a" TyInt))]
                (TyConApp "Int" []))]
         (TyConApp "Int" [])

[]
==============================================
fromList [("Bool",TyAlg "Bool" [("True",-5,TyConApp "Bool" [],[]),("False",-6,TyConApp "Bool" [],[])]),("Char",TyAlg "Char" [("Char!",-4,TyConApp "Char" [],[TyChar])]),("Double",TyAlg "Double" [("Double!",-3,TyConApp "Double" [],[TyReal])]),("Float",TyAlg "Float" [("Float!",-2,TyConApp "Float" [],[TyReal])]),("Int",TyAlg "Int" [("Int!",-1,TyConApp "Int" [],[TyInt])])]
fromList [("a",App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 123) TyInt)),("aa",Const (CInt 123) TyInt),("b",App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 456) TyInt)),("baa",Const (CInt 456) TyInt),("test1",Case (Var "a" (TyConApp "Int" [])) [((("Int!",-1,TyConApp "Int" [],[TyInt]),["a"]),Case (Var "b" (TyConApp "Int" [])) [((("Int!",-1,TyConApp "Int" [],[TyInt]),["b"]),App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Var "a" TyInt))] (TyConApp "Int" []))] (TyConApp "Int" []))]

>>> App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 123) TyInt)

[(App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 456) TyInt),(("Int!",-1,TyConApp "Int" [],[TyInt]),["baa"])),(App (DCon ("Int!",-1,TyConApp "Int" [],[TyInt]) (TyConApp "Int" [])) (Const (CInt 123) TyInt),(("Int!",-1,TyConApp "Int" [],[TyInt]),["aa"]))]
Compiles!
