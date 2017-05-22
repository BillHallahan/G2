RAW CORE
%module Peano (Safe) [r0 :-> Data constructor ‘Zero’,
                      r1 :-> Data constructor ‘Succ’, r2 :-> Type constructor ‘Peano’,
                      r3 :-> Identifier ‘pue’, r4 :-> Identifier ‘eqtest’,
                      r5 :-> Identifier ‘add’, rfh :-> Identifier ‘Zero’,
                      rgf :-> Identifier ‘Succ’]
add [Occ=LoopBreaker] :: Peano -> Peano -> Peano
[GblId, Arity=2, Caf=NoCafRefs, Str=DmdType]
add =
  \ (ds :: Peano) (b :: Peano) ->
    case ds of _ [Occ=Dead] {
      Zero -> b;
      Succ a -> Succ (add a b)
    };
eqtest :: forall a a1. (Eq a, Num a, Num a1) => a -> a1
[GblId, Arity=4, Caf=NoCafRefs, Str=DmdType]
eqtest =
  \ (@ a)
    (@ a1)
    ($dEq :: Eq a)
    ($dNum :: Num a)
    ($dNum1 :: Num a1)
    (a2 :: a) ->
    case == @ a $dEq a2 (fromInteger @ a $dNum (__integer 3))
    of _ [Occ=Dead] {
      False -> fromInteger @ a1 $dNum1 (__integer 5);
      True -> fromInteger @ a1 $dNum1 (__integer 2)
    }
pue :: Int -> Int
[GblId, Arity=1, Caf=NoCafRefs, Str=DmdType]
pue =
  \ (ds :: Int) ->
    case ds of wild { I# ds1 ->
    case ds1 of _ [Occ=Dead] {
      __DEFAULT -> wild;
      123 -> I# 0
    }
    }
INIT STATE
(fromList [("Bool",TyAlg "Bool" [DC ("True",-5,TyConApp "Bool" [],[]),DC ("False",-6,TyConApp "Bool" [],[])]),("Char",TyAlg "Char" [DC ("C#",-4,TyConApp "Char" [],[TyRawChar])]),("Double",TyAlg "Double" [DC ("D#",-3,TyConApp "Double" [],[TyRawDouble])]),("Float",TyAlg "Float" [DC ("F#",-2,TyConApp "Float" [],[TyRawFloat])]),("Int",TyAlg "Int" [DC ("I#",-1,TyConApp "Int" [],[TyRawInt])]),("Peano",TyAlg "Peano" [DC ("Zero",1,TyConApp "Peano" [],[]),DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []])])]

,fromList
[("add",Lam "ds" (Lam "b" (App (Lam "wild" (Case (Var "ds" (TyConApp "Peano" [])) [(Alt (DC ("Zero",1,TyConApp "Peano" [],[]),[]),Var "b" (TyConApp "Peano" [])),(Alt (DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []]),["a"]),App (Var "Succ" (TyFun (TyConApp "Peano" []) (TyConApp "Peano" []))) (App (App (Var "add" (TyFun (TyConApp "Peano" []) (TyFun (TyConApp "Peano" []) (TyConApp "Peano" [])))) (Var "a" (TyConApp "Peano" []))) (Var "b" (TyConApp "Peano" []))))] (TyConApp "Peano" [])) (TyFun (TyConApp "Peano" []) (TyConApp "Peano" []))) (Var "ds" (TyConApp "Peano" []))) (TyFun (TyConApp "Peano" []) (TyConApp "Peano" []))) (TyFun (TyConApp "Peano" []) (TyFun (TyConApp "Peano" []) (TyConApp "Peano" []))))

,("eqtest",Lam "a" (Lam "a1" (Lam "$dEq" (Lam "$dNum" (Lam "$dNum1" (Lam "a2" (App (Lam "wild" (Case (App (App (App (App (Var "==" (TyForAll "a" (TyFun (TyConApp "Eq" [TyVar "a"]) (TyFun (TyVar "a") (TyFun (TyVar "a") (TyConApp "Bool" [])))))) (Type (TyVar "a"))) (Var "$dEq" (TyConApp "Eq" [TyVar "a"]))) (Var "a2" (TyVar "a"))) (App (App (App (Var "fromInteger" (TyForAll "a" (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Integer" []) (TyVar "a"))))) (Type (TyVar "a"))) (Var "$dNum" (TyConApp "Num" [TyVar "a"]))) (Const (CInt 3)))) [(Alt (DC ("False",1,TyConApp "Bool" [],[]),[]),App (App (App (Var "fromInteger" (TyForAll "a" (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Integer" []) (TyVar "a"))))) (Type (TyVar "a1"))) (Var "$dNum1" (TyConApp "Num" [TyVar "a1"]))) (Const (CInt 5))),(Alt (DC ("True",2,TyConApp "Bool" [],[]),[]),App (App (App (Var "fromInteger" (TyForAll "a" (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Integer" []) (TyVar "a"))))) (Type (TyVar "a1"))) (Var "$dNum1" (TyConApp "Num" [TyVar "a1"]))) (Const (CInt 2)))] (TyVar "a1")) (TyFun (TyConApp "Bool" []) (TyVar "a1"))) (App (App (App (App (Var "==" (TyForAll "a" (TyFun (TyConApp "Eq" [TyVar "a"]) (TyFun (TyVar "a") (TyFun (TyVar "a") (TyConApp "Bool" [])))))) (Type (TyVar "a"))) (Var "$dEq" (TyConApp "Eq" [TyVar "a"]))) (Var "a2" (TyVar "a"))) (App (App (App (Var "fromInteger" (TyForAll "a" (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Integer" []) (TyVar "a"))))) (Type (TyVar "a"))) (Var "$dNum" (TyConApp "Num" [TyVar "a"]))) (Const (CInt 3))))) (TyFun (TyVar "a") (TyVar "a1"))) (TyFun (TyConApp "Num" [TyVar "a1"]) (TyFun (TyVar "a") (TyVar "a1")))) (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a1"]) (TyFun (TyVar "a") (TyVar "a1"))))) (TyFun (TyConApp "Eq" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a1"]) (TyFun (TyVar "a") (TyVar "a1")))))) (TyForAll "a1" (TyFun (TyConApp "Eq" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a1"]) (TyFun (TyVar "a") (TyVar "a1"))))))) (TyForAll "a" (TyForAll "a1" (TyFun (TyConApp "Eq" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyConApp "Num" [TyVar "a1"]) (TyFun (TyVar "a") (TyVar "a1"))))))))

,("pue",Lam "ds"
            (App (Lam "wild"
                      (Case (Var "ds" (TyConApp "Int" []))
                            [(Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),
                                Case (App (App (App (App (Var "==" TyBottom) (Type TyBottom)) (Var "$dEq" TyBottom)) (App (DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))) (Var "ds1" TyRawInt))) (App (DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))) (Const (CInt 123))))
                                     [(Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),
                                         App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 0))),
                                      (Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),
                                         Var "wild" (TyConApp "Int" []))] (TyConApp "Int" []))]
                            (TyConApp "Int" []))
                      (TyFun (TyConApp "Int" []) (TyConApp "Int" [])))
                 (Var "ds" (TyConApp "Int" [])))
            (TyFun (TyConApp "Int" []) (TyConApp "Int" [])))],

App (Lam "wild" (Case (Var "dsd" (TyConApp "Int" [])) [(Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),Case (App (App (App (App (Var "==" TyBottom) (Type TyBottom)) (Var "$dEq" TyBottom)) (App (DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))) (Var "ds1" TyRawInt))) (App (DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))) (Const (CInt 123)))) [(Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 0))),(Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),Var "wild" (TyConApp "Int" []))] (TyConApp "Int" []))] (TyConApp "Int" [])) (TyFun (TyConApp "Int" []) (TyConApp "Int" []))) (Var "dsd" (TyConApp "Int" [])),[])
mkStateStr of INIT STATE
> Type Env:
Bool
    TyAlg "Bool" [DC ("True",-5,TyConApp "Bool" [],[]),DC ("False",-6,TyConApp "Bool" [],[])]
Char
    TyAlg "Char" [DC ("C#",-4,TyConApp "Char" [],[TyRawChar])]
Double
    TyAlg "Double" [DC ("D#",-3,TyConApp "Double" [],[TyRawDouble])]
Float
    TyAlg "Float" [DC ("F#",-2,TyConApp "Float" [],[TyRawFloat])]
Int
    TyAlg "Int" [DC ("I#",-1,TyConApp "Int" [],[TyRawInt])]
Peano
    TyAlg "Peano" [DC ("Zero",1,TyConApp "Peano" [],[]),DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []])]

> Expr Env:
add
    Lam ("ds"
   Lam ("b"
      App (
         Lam ("wild"
            Case (
               Var ds (TyConApp "Peano" [])
               (Alt (DC ("Zero",1,TyConApp "Peano" [],[]),[]),
                  Var b (TyConApp "Peano" []))
               (Alt (DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []]),["a"]),
                  App (
                     Var Succ (TyFun (
                           TyConApp "Peano" []
                           TyConApp "Peano" []
                        ))
                     App (
                        App (
                           Var add (TyFun (
                                 TyConApp "Peano" []
                                 TyFun (
                                    TyConApp "Peano" []
                                    TyConApp "Peano" []
                                 )
                              ))
                           Var a (TyConApp "Peano" [])
                        )
                        Var b (TyConApp "Peano" [])
                     )
                  ))
 TyConApp "Peano" []) TyFun (
            TyConApp "Peano" []
            TyConApp "Peano" []
         ))
         Var ds (TyConApp "Peano" [])
      ) TyFun (
      TyConApp "Peano" []
      TyConApp "Peano" []
   )) TyFun (
   TyConApp "Peano" []
   TyFun (
      TyConApp "Peano" []
      TyConApp "Peano" []
   )
))
eqtest
    Lam ("a"
   Lam ("a1"
      Lam ("$dEq"
         Lam ("$dNum"
            Lam ("$dNum1"
               Lam ("a2"
                  App (
                     Lam ("wild"
                        Case (
                           App (
                              App (
                                 App (
                                    App (
                                       Var == (TyForAll "a"(TyFun (
                                                TyConApp "Eq" [ TyVar "a"]
                                                TyFun ( TyVar "a"
                                                   TyFun ( TyVar "a"
                                                      TyConApp "Bool" []
                                                   )
                                                )
                                             )))
                                       Type (TyVar "a")
                                    )
                                    Var $dEq (TyConApp "Eq" [TyVar "a"])
                                 )
                                 Var a2 (TyVar "a")
                              )
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a")
                                    )
                                    Var $dNum (TyConApp "Num" [TyVar "a"])
                                 )
                                 Const (CInt 3)
                              )
                           )
                           (Alt (DC ("False",1,TyConApp "Bool" [],[]),[]),
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a1")
                                    )
                                    Var $dNum1 (TyConApp "Num" [TyVar "a1"])
                                 )
                                 Const (CInt 5)
                              ))
                           (Alt (DC ("True",2,TyConApp "Bool" [],[]),[]),
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a1")
                                    )
                                    Var $dNum1 (TyConApp "Num" [TyVar "a1"])
                                 )
                                 Const (CInt 2)
                              ))
 TyVar "a1") TyFun (
                        TyConApp "Bool" [] TyVar "a1"
                     ))
                     App (
                        App (
                           App (
                              App (
                                 Var == (TyForAll "a"(TyFun (
                                          TyConApp "Eq" [ TyVar "a"]
                                          TyFun ( TyVar "a"
                                             TyFun ( TyVar "a"
                                                TyConApp "Bool" []
                                             )
                                          )
                                       )))
                                 Type (TyVar "a")
                              )
                              Var $dEq (TyConApp "Eq" [TyVar "a"])
                           )
                           Var a2 (TyVar "a")
                        )
                        App (
                           App (
                              App (
                                 Var fromInteger (TyForAll "a"(TyFun (
                                          TyConApp "Num" [ TyVar "a"]
                                          TyFun (
                                             TyConApp "Integer" [] TyVar "a"
                                          )
                                       )))
                                 Type (TyVar "a")
                              )
                              Var $dNum (TyConApp "Num" [TyVar "a"])
                           )
                           Const (CInt 3)
                        )
                     )
                  ) TyFun ( TyVar "a" TyVar "a1"
               )) TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )) TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )) TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      )) TyForAll "a1"(TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      ))) TyForAll "a"(TyForAll "a1"(TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      ))))
pue
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Int" [])
            (Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),
               Case (
                  App (
                     App (
                        App (
                           App (
                              Var == (TyBottom)
                              Type (TyBottom)
                           )
                           Var $dEq (TyBottom)
                        )
                        App (
                           DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                           Var ds1 (TyRawInt)
                        )
                     )
                     App (
                        DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                        Const (CInt 123)
                     )
                  )
                  (Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 0)
                     ))
                  (Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),
                     Var wild (TyConApp "Int" []))
 TyConApp "Int" []))
 TyConApp "Int" []) TyFun (
         TyConApp "Int" []
         TyConApp "Int" []
      ))
      Var ds (TyConApp "Int" [])
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))

> Curr Expr:
App (
   Lam ("wild"
      Case (
         Var dsd (TyConApp "Int" [])
         (Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),
            Case (
               App (
                  App (
                     App (
                        App (
                           Var == (TyBottom)
                           Type (TyBottom)
                        )
                        Var $dEq (TyBottom)
                     )
                     App (
                        DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                        Var ds1 (TyRawInt)
                     )
                  )
                  App (
                     DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                     Const (CInt 123)
                  )
               )
               (Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 0)
                  ))
               (Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),
                  Var wild (TyConApp "Int" []))
 TyConApp "Int" []))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   ))
   Var dsd (TyConApp "Int" [])
)

> Path Constraints:

HIGHER
[]
[]
+++++++++++++++++++++++++
> Type Env:
Bool
    TyAlg "Bool" [DC ("True",-5,TyConApp "Bool" [],[]),DC ("False",-6,TyConApp "Bool" [],[])]
Char
    TyAlg "Char" [DC ("C#",-4,TyConApp "Char" [],[TyRawChar])]
Double
    TyAlg "Double" [DC ("D#",-3,TyConApp "Double" [],[TyRawDouble])]
Float
    TyAlg "Float" [DC ("F#",-2,TyConApp "Float" [],[TyRawFloat])]
Int
    TyAlg "Int" [DC ("I#",-1,TyConApp "Int" [],[TyRawInt])]
Peano
    TyAlg "Peano" [DC ("Zero",1,TyConApp "Peano" [],[]),DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []])]

> Expr Env:
add
    Lam ("ds"
   Lam ("b"
      App (
         Lam ("wild"
            Case (
               Var ds (TyConApp "Peano" [])
               (Alt (DC ("Zero",1,TyConApp "Peano" [],[]),[]),
                  Var b (TyConApp "Peano" []))
               (Alt (DC ("Succ",2,TyConApp "Peano" [],[TyConApp "Peano" []]),["a"]),
                  App (
                     Var Succ (TyFun (
                           TyConApp "Peano" []
                           TyConApp "Peano" []
                        ))
                     App (
                        App (
                           Var add (TyFun (
                                 TyConApp "Peano" []
                                 TyFun (
                                    TyConApp "Peano" []
                                    TyConApp "Peano" []
                                 )
                              ))
                           Var a (TyConApp "Peano" [])
                        )
                        Var b (TyConApp "Peano" [])
                     )
                  ))
 TyConApp "Peano" []) TyFun (
            TyConApp "Peano" []
            TyConApp "Peano" []
         ))
         Var ds (TyConApp "Peano" [])
      ) TyFun (
      TyConApp "Peano" []
      TyConApp "Peano" []
   )) TyFun (
   TyConApp "Peano" []
   TyFun (
      TyConApp "Peano" []
      TyConApp "Peano" []
   )
))
eqtest
    Lam ("a"
   Lam ("a1"
      Lam ("$dEq"
         Lam ("$dNum"
            Lam ("$dNum1"
               Lam ("a2"
                  App (
                     Lam ("wild"
                        Case (
                           App (
                              App (
                                 App (
                                    App (
                                       Var == (TyForAll "a"(TyFun (
                                                TyConApp "Eq" [ TyVar "a"]
                                                TyFun ( TyVar "a"
                                                   TyFun ( TyVar "a"
                                                      TyConApp "Bool" []
                                                   )
                                                )
                                             )))
                                       Type (TyVar "a")
                                    )
                                    Var $dEq (TyConApp "Eq" [TyVar "a"])
                                 )
                                 Var a2 (TyVar "a")
                              )
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a")
                                    )
                                    Var $dNum (TyConApp "Num" [TyVar "a"])
                                 )
                                 Const (CInt 3)
                              )
                           )
                           (Alt (DC ("False",1,TyConApp "Bool" [],[]),[]),
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a1")
                                    )
                                    Var $dNum1 (TyConApp "Num" [TyVar "a1"])
                                 )
                                 Const (CInt 5)
                              ))
                           (Alt (DC ("True",2,TyConApp "Bool" [],[]),[]),
                              App (
                                 App (
                                    App (
                                       Var fromInteger (TyForAll "a"(TyFun (
                                                TyConApp "Num" [ TyVar "a"]
                                                TyFun (
                                                   TyConApp "Integer" [] TyVar "a"
                                                )
                                             )))
                                       Type (TyVar "a1")
                                    )
                                    Var $dNum1 (TyConApp "Num" [TyVar "a1"])
                                 )
                                 Const (CInt 2)
                              ))
 TyVar "a1") TyFun (
                        TyConApp "Bool" [] TyVar "a1"
                     ))
                     App (
                        App (
                           App (
                              App (
                                 Var == (TyForAll "a"(TyFun (
                                          TyConApp "Eq" [ TyVar "a"]
                                          TyFun ( TyVar "a"
                                             TyFun ( TyVar "a"
                                                TyConApp "Bool" []
                                             )
                                          )
                                       )))
                                 Type (TyVar "a")
                              )
                              Var $dEq (TyConApp "Eq" [TyVar "a"])
                           )
                           Var a2 (TyVar "a")
                        )
                        App (
                           App (
                              App (
                                 Var fromInteger (TyForAll "a"(TyFun (
                                          TyConApp "Num" [ TyVar "a"]
                                          TyFun (
                                             TyConApp "Integer" [] TyVar "a"
                                          )
                                       )))
                                 Type (TyVar "a")
                              )
                              Var $dNum (TyConApp "Num" [TyVar "a"])
                           )
                           Const (CInt 3)
                        )
                     )
                  ) TyFun ( TyVar "a" TyVar "a1"
               )) TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )) TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )) TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      )) TyForAll "a1"(TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      ))) TyForAll "a"(TyForAll "a1"(TyFun (
         TyConApp "Eq" [ TyVar "a"]
         TyFun (
            TyConApp "Num" [ TyVar "a"]
            TyFun (
               TyConApp "Num" [ TyVar "a1"]
               TyFun ( TyVar "a" TyVar "a1"
               )
            )
         )
      ))))
pue
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Int" [])
            (Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),
               Case (
                  App (
                     App (
                        App (
                           App (
                              Var == (TyBottom)
                              Type (TyBottom)
                           )
                           Var $dEq (TyBottom)
                        )
                        App (
                           DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                           Var ds1 (TyRawInt)
                        )
                     )
                     App (
                        DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                        Const (CInt 123)
                     )
                  )
                  (Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 0)
                     ))
                  (Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),
                     Var wild (TyConApp "Int" []))
 TyConApp "Int" []))
 TyConApp "Int" []) TyFun (
         TyConApp "Int" []
         TyConApp "Int" []
      ))
      Var ds (TyConApp "Int" [])
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))

> Curr Expr:
App (
   Lam ("wild"
      Case (
         Var dsd (TyConApp "Int" [])
         (Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1"]),
            Case (
               App (
                  App (
                     App (
                        App (
                           Var == (TyBottom)
                           Type (TyBottom)
                        )
                        Var $dEq (TyBottom)
                     )
                     App (
                        DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                        Var ds1 (TyRawInt)
                     )
                  )
                  App (
                     DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
                     Const (CInt 123)
                  )
               )
               (Alt (DC ("True",-5,TyConApp "Bool" [],[]),[]),
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 0)
                  ))
               (Alt (DC ("False",-6,TyConApp "Bool" [],[]),[]),
                  Var wild (TyConApp "Int" []))
 TyConApp "Int" []))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   ))
   Var dsd (TyConApp "Int" [])
)

> Path Constraints:

=======================
Number of execution states: 2
Compiles!


App (
   App (
      App (
         App (
            Var == (TyBottom)
            Type (TyBottom)
         )
         Var $dEq (TyBottom)
      )
      App (
         DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
         Var ds1d (TyRawInt)
      )
   )
   App (
      DCon (DC ("I#",-1,TyConApp "Int" [],[TyRawInt]))
      Const (CInt 123)
   )
) = Alt (DC ("False",-6,TyConApp "Bool" [],[]),[])
--AND--
Var dsd (TyConApp "Int" []) = Alt (DC ("I#",1,TyConApp "Int" [],[TyRawInt]),["ds1d"])
 => 
