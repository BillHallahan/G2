(fromList [("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")],[])
======================================
(fromList [("a",App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),("b",App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b"))),("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")],[(App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),(("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["b","a"]))])
======================================
(fromList [("a",App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),("b",App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b"))),("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Case (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")],[(App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),(("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["b","a"]))])
=====================================
(fromList [("a",App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),("aa",Var "c"),("b",App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b"))),("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Var "aa",[(App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"),(("Leaf",1,[TyConApp "Int" []]),["aa"])),(App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),(("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["b","a"]))])
=====================================
(fromList [("a",App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),("aa",Var "c"),("b",App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b"))),("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Var "c",[(App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"),(("Leaf",1,[TyConApp "Int" []]),["aa"])),(App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),(("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["b","a"]))])
=====================================
(fromList [("a",App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),("aa",Var "c"),("b",App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b"))),("test1",Case (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"))) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Case (Var "a") [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")]),("test2",Case (App (App (Var "a") (Var "b")) (Var "c")) [((("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["a","b"]),Var "a"),((("Leaf",1,[TyConApp "Int" []]),["a"]),Var "a")])],Var "c",[(App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c"),(("Leaf",1,[TyConApp "Int" []]),["aa"])),(App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (App (DCon ("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []])) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "a"))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "b")))) (App (DCon ("Leaf",1,[TyConApp "Int" []])) (Var "c")),(("Node",2,[TyConApp "Tree" [],TyConApp "Tree" []]),["b","a"]))])
