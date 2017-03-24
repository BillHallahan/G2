%module DataTypes (Safe) [r0 :-> Data constructor ‘I’,
                          r1 :-> Data constructor ‘H’, r2 :-> Data constructor ‘G’,
                          r3 :-> Type constructor ‘Y’, r4 :-> Data constructor ‘F’,
                          r5 :-> Data constructor ‘E’, r6 :-> Data constructor ‘D’,
                          r7 :-> Data constructor ‘C’, r8 :-> Data constructor ‘B’,
                          r9 :-> Data constructor ‘A’, ra :-> Type constructor ‘X’,
                          rb :-> Identifier ‘xApp2’, rc :-> Identifier ‘xApp’,
                          rd :-> Identifier ‘intToInt’, re :-> Identifier ‘g’,
                          rf :-> Identifier ‘f’, r4f :-> Identifier ‘A’,
                          r4h :-> Identifier ‘B’, r4i :-> Identifier ‘C’,
                          r4j :-> Identifier ‘D’, r4k :-> Identifier ‘E’,
                          r4l :-> Identifier ‘F’, r4m :-> Identifier ‘G’,
                          r4o :-> Identifier ‘H’, r4p :-> Identifier ‘I’]
f :: X -> X
[GblId, Arity=1, Caf=NoCafRefs, Str=DmdType]
f =
  \ (ds :: X) ->
    case ds of wild {
      __DEFAULT -> wild;
      A ds1 ->
        case ds1 of _ [Occ=Dead] {
          __DEFAULT -> B;
          G -> C
        };
      B -> A (H (I# 8));
      C -> C;
      D h -> F (h (I# 8))
    }
g :: Y -> X
[GblId, Arity=1, Caf=NoCafRefs, Str=DmdType]
g =
  \ (ds :: Y) ->
    case ds of _ [Occ=Dead] {
      __DEFAULT -> C;
      G -> B
    }
intToInt :: Int -> Int
[GblId, Arity=1, Str=DmdType]
intToInt = \ (x :: Int) -> + @ Int $fNumInt x (I# 3)
xApp2 :: X
[GblId, Str=DmdType]
xApp2 = E intToInt intToInt
xApp :: X
[GblId, Str=DmdType]
xApp = D intToInt
(fromList [("Bool",TyAlg "Bool" [DC ("True",-5,TyConApp "Bool" [],[]),DC ("False",-6,TyConApp "Bool" [],[])]),("Char",TyAlg "Char" [DC ("C#",-4,TyConApp "Char" [],[TyRawChar])]),("Double",TyAlg "Double" [DC ("D#",-3,TyConApp "Double" [],[TyRawDouble])]),("Float",TyAlg "Float" [DC ("F#",-2,TyConApp "Float" [],[TyRawFloat])]),("Int",TyAlg "Int" [DC ("I#",-1,TyConApp "Int" [],[TyRawInt])]),("X",TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),DC ("E",5,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" []),TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]),("Y",TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])])],fromList [("f",Lam "ds" (App (Lam "wild" (Case (Var "ds" (TyConApp "X" [])) [(Alt (DC ("DEFAULT",0,TyBottom,[]),[]),Var "wild" (TyConApp "X" [])),(Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),App (Lam "wild1" (Case (Var "ds1" (TyConApp "Y" [])) [(Alt (DC ("DEFAULT",0,TyBottom,[]),[]),Var "B" (TyConApp "X" [])),(Alt (DC ("G",1,TyConApp "Y" [],[]),[]),Var "C" (TyConApp "X" []))] (TyConApp "X" [])) (TyFun (TyConApp "Y" []) (TyConApp "X" []))) (Var "ds1" (TyConApp "Y" []))),(Alt (DC ("B",2,TyConApp "X" [],[]),[]),App (Var "A" (TyFun (TyConApp "Y" []) (TyConApp "X" []))) (App (Var "H" (TyFun (TyConApp "Int" []) (TyConApp "Y" []))) (App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 8))))),(Alt (DC ("C",3,TyConApp "X" [],[]),[]),Var "C" (TyConApp "X" [])),(Alt (DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),["h"]),App (Var "F" (TyFun (TyConApp "Int" []) (TyConApp "X" []))) (App (Var "h" (TyFun (TyConApp "Int" []) (TyConApp "Int" []))) (App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 8)))))] (TyConApp "X" [])) (TyFun (TyConApp "X" []) (TyConApp "X" []))) (Var "ds" (TyConApp "X" []))) (TyFun (TyConApp "X" []) (TyConApp "X" []))),("g",Lam "ds" (App (Lam "wild" (Case (Var "ds" (TyConApp "Y" [])) [(Alt (DC ("DEFAULT",0,TyBottom,[]),[]),Var "C" (TyConApp "X" [])),(Alt (DC ("G",1,TyConApp "Y" [],[]),[]),Var "B" (TyConApp "X" []))] (TyConApp "X" [])) (TyFun (TyConApp "Y" []) (TyConApp "X" []))) (Var "ds" (TyConApp "Y" []))) (TyFun (TyConApp "Y" []) (TyConApp "X" []))),("intToInt",Lam "x" (App (App (App (App (Var "+" (TyForAll "a" (TyFun (TyConApp "Num" [TyVar "a"]) (TyFun (TyVar "a") (TyFun (TyVar "a") (TyVar "a")))))) (Type (TyConApp "Int" []))) (Var "$fNumInt" (TyConApp "Num" [TyConApp "Int" []]))) (Var "x" (TyConApp "Int" []))) (App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 3)))) (TyFun (TyConApp "Int" []) (TyConApp "Int" []))),("xApp",App (Var "D" (TyFun (TyFun (TyConApp "Int" []) (TyConApp "Int" [])) (TyConApp "X" []))) (Var "intToInt" (TyFun (TyConApp "Int" []) (TyConApp "Int" [])))),("xApp2",App (App (Var "E" (TyFun (TyFun (TyConApp "Int" []) (TyConApp "Int" [])) (TyFun (TyFun (TyConApp "Int" []) (TyConApp "Int" [])) (TyConApp "X" [])))) (Var "intToInt" (TyFun (TyConApp "Int" []) (TyConApp "Int" [])))) (Var "intToInt" (TyFun (TyConApp "Int" []) (TyConApp "Int" []))))],App (Lam "wild" (Case (Var "dsd" (TyConApp "X" [])) [(Alt (DC ("DEFAULT",0,TyBottom,[]),[]),Var "wild" (TyConApp "X" [])),(Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),App (Lam "wild1" (Case (Var "ds1" (TyConApp "Y" [])) [(Alt (DC ("DEFAULT",0,TyBottom,[]),[]),Var "B" (TyConApp "X" [])),(Alt (DC ("G",1,TyConApp "Y" [],[]),[]),Var "C" (TyConApp "X" []))] (TyConApp "X" [])) (TyFun (TyConApp "Y" []) (TyConApp "X" []))) (Var "ds1" (TyConApp "Y" []))),(Alt (DC ("B",2,TyConApp "X" [],[]),[]),App (Var "A" (TyFun (TyConApp "Y" []) (TyConApp "X" []))) (App (Var "H" (TyFun (TyConApp "Int" []) (TyConApp "Y" []))) (App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 8))))),(Alt (DC ("C",3,TyConApp "X" [],[]),[]),Var "C" (TyConApp "X" [])),(Alt (DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),["h"]),App (Var "F" (TyFun (TyConApp "Int" []) (TyConApp "X" []))) (App (Var "h" (TyFun (TyConApp "Int" []) (TyConApp "Int" []))) (App (Var "I#" (TyFun TyRawInt (TyConApp "Int" []))) (Const (CInt 8)))))] (TyConApp "X" [])) (TyFun (TyConApp "X" []) (TyConApp "X" []))) (Var "dsd" (TyConApp "X" [])),[])
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),DC ("E",5,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" []),TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]

> Expr Env:
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     Var h (TyFun (
                           TyConApp "Int" []
                           TyConApp "Int" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
xApp
    App (
   Var D (TyFun (
         TyFun (
            TyConApp "Int" []
            TyConApp "Int" []
         )
         TyConApp "X" []
      ))
   Var intToInt (TyFun (
         TyConApp "Int" []
         TyConApp "Int" []
      ))
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyFun (
               TyConApp "Int" []
               TyConApp "Int" []
            )
            TyFun (
               TyFun (
                  TyConApp "Int" []
                  TyConApp "Int" []
               )
               TyConApp "X" []
            )
         ))
      Var intToInt (TyFun (
            TyConApp "Int" []
            TyConApp "Int" []
         ))
   )
   Var intToInt (TyFun (
         TyConApp "Int" []
         TyConApp "Int" []
      ))
)

> Curr Expr:
App (
   Lam ("wild"
      Case (
         Var dsd (TyConApp "X" [])
         (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
            Var wild (TyConApp "X" []))
         (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
            App (
               Lam ("wild1"
                  Case (
                     Var ds1 (TyConApp "Y" [])
                     (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                        Var B (TyConApp "X" []))
                     (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                        Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                  TyConApp "Y" []
                  TyConApp "X" []
               ))
               Var ds1 (TyConApp "Y" [])
            ))
         (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
            App (
               Var A (TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
               App (
                  Var H (TyFun (
                        TyConApp "Int" []
                        TyConApp "Y" []
                     ))
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 8)
                  )
               )
            ))
         (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
            Var C (TyConApp "X" []))
         (Alt (DC ("D",4,TyConApp "X" [],[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]),["h"]),
            App (
               Var F (TyFun (
                     TyConApp "Int" []
                     TyConApp "X" []
                  ))
               App (
                  Var h (TyFun (
                        TyConApp "Int" []
                        TyConApp "Int" []
                     ))
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 8)
                  )
               )
            ))
 TyConApp "X" []) TyFun (
      TyConApp "X" []
      TyConApp "X" []
   ))
   Var dsd (TyConApp "X" [])
)

> Path Constraints:

HIGHER
[TyFun (TyConApp "Int" []) (TyConApp "Int" [])]
[("h",TyFun (TyConApp "Int" []) (TyConApp "Int" [])),("intToInt",TyFun (TyConApp "Int" []) (TyConApp "Int" []))]
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
App (
   Lam ("wild"
      Case (
         Var dsd (TyConApp "X" [])
         (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
            Var wild (TyConApp "X" []))
         (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
            App (
               Lam ("wild1"
                  Case (
                     Var ds1 (TyConApp "Y" [])
                     (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                        Var B (TyConApp "X" []))
                     (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                        Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                  TyConApp "Y" []
                  TyConApp "X" []
               ))
               Var ds1 (TyConApp "Y" [])
            ))
         (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
            App (
               Var A (TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
               App (
                  Var H (TyFun (
                        TyConApp "Int" []
                        TyConApp "Y" []
                     ))
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 8)
                  )
               )
            ))
         (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
            Var C (TyConApp "X" []))
         (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
            App (
               Var F (TyFun (
                     TyConApp "Int" []
                     TyConApp "X" []
                  ))
               App (
                  App (
                     Var apply (TyFun (
                           TyConApp "applyType" []
                           TyFun (
                              TyConApp "Int" []
                              TyConApp "Int" []
                           )
                        ))
                     Var h (TyConApp "applyType" [])
                  )
                  App (
                     Var I# (TyFun ( TyRawInt
                           TyConApp "Int" []
                        ))
                     Const (CInt 8)
                  )
               )
            ))
 TyConApp "X" []) TyFun (
      TyConApp "X" []
      TyConApp "X" []
   ))
   Var dsd (TyConApp "X" [])
)

> Path Constraints:

=======================
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
App (
   Var A (TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
   App (
      Var H (TyFun (
            TyConApp "Int" []
            TyConApp "Y" []
         ))
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 8)
      )
   )
)

> Path Constraints:
Var dsd (TyConApp "X" []) = Alt (DC ("B",2,TyConApp "X" [],[]),[])
--------------
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
Var C (TyConApp "X" [])

> Path Constraints:
Var dsd (TyConApp "X" []) = Alt (DC ("C",3,TyConApp "X" [],[]),[])
--------------
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
a
    Var hh (TyConApp "applyType" [])
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
i
    App (
   Var I# (TyFun ( TyRawInt
         TyConApp "Int" []
      ))
   Const (CInt 8)
)
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
App (
   Var F (TyFun (
         TyConApp "Int" []
         TyConApp "X" []
      ))
   Case (
      Var a (TyAlg "applyType" [])
      (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
         App (
            Var intToInt (TyFun (
                  TyConApp "Int" []
                  TyConApp "Int" []
               ))
            Var i (TyConApp "Int" [])
         ))
 TyConApp "Int" [])
)

> Path Constraints:
Var dsd (TyConApp "X" []) = Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["hh"])
--------------
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
Var dsd (TyConApp "X" [])

> Path Constraints:
Var dsd (TyConApp "X" []) != Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"])
--AND--
Var dsd (TyConApp "X" []) != Alt (DC ("B",2,TyConApp "X" [],[]),[])
--AND--
Var dsd (TyConApp "X" []) != Alt (DC ("C",3,TyConApp "X" [],[]),[])
--AND--
Var dsd (TyConApp "X" []) != Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"])
--------------
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
wild1
    Var ds1d (TyConApp "Y" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
Var C (TyConApp "X" [])

> Path Constraints:
Var ds1d (TyConApp "Y" []) = Alt (DC ("G",1,TyConApp "Y" [],[]),[])
--AND--
Var dsd (TyConApp "X" []) = Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1d"])
--------------
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
X
    TyAlg "X" [DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),DC ("B",2,TyConApp "X" [],[]),DC ("C",3,TyConApp "X" [],[]),DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),DC ("E",5,TyConApp "X" [],[TyConApp "applyType" [],TyConApp "applyType" []]),DC ("F",6,TyConApp "X" [],[TyConApp "Int" []])]
Y
    TyAlg "Y" [DC ("G",1,TyConApp "Y" [],[]),DC ("H",2,TyConApp "Y" [],[TyConApp "Int" []]),DC ("I",3,TyConApp "Y" [],[])]
applyType
    TyAlg "applyType" [DC ("applyCon",-7,TyConApp "applyType" [],[])]

> Expr Env:
apply
    Lam ("a"
   Lam ("i"
      Case (
         Var a (TyAlg "applyType" [])
         (Alt (DC ("applyCon",-1000,TyConApp "applyType" [],[]),["new"]),
            App (
               Var intToInt (TyFun (
                     TyConApp "Int" []
                     TyConApp "Int" []
                  ))
               Var i (TyConApp "Int" [])
            ))
 TyConApp "Int" []) TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )) TyFun ( TyAlg "applyType" []
   TyFun (
      TyConApp "Int" []
      TyConApp "Int" []
   )
))
f
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "X" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var wild (TyConApp "X" []))
            (Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1"]),
               App (
                  Lam ("wild1"
                     Case (
                        Var ds1 (TyConApp "Y" [])
                        (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
                           Var B (TyConApp "X" []))
                        (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
                           Var C (TyConApp "X" []))
 TyConApp "X" []) TyFun (
                     TyConApp "Y" []
                     TyConApp "X" []
                  ))
                  Var ds1 (TyConApp "Y" [])
               ))
            (Alt (DC ("B",2,TyConApp "X" [],[]),[]),
               App (
                  Var A (TyFun (
                        TyConApp "Y" []
                        TyConApp "X" []
                     ))
                  App (
                     Var H (TyFun (
                           TyConApp "Int" []
                           TyConApp "Y" []
                        ))
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
            (Alt (DC ("C",3,TyConApp "X" [],[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("D",4,TyConApp "X" [],[TyConApp "applyType" []]),["h"]),
               App (
                  Var F (TyFun (
                        TyConApp "Int" []
                        TyConApp "X" []
                     ))
                  App (
                     App (
                        Var apply (TyFun (
                              TyConApp "applyType" []
                              TyFun (
                                 TyConApp "Int" []
                                 TyConApp "Int" []
                              )
                           ))
                        Var h (TyConApp "applyType" [])
                     )
                     App (
                        Var I# (TyFun ( TyRawInt
                              TyConApp "Int" []
                           ))
                        Const (CInt 8)
                     )
                  )
               ))
 TyConApp "X" []) TyFun (
         TyConApp "X" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "X" [])
   ) TyFun (
   TyConApp "X" []
   TyConApp "X" []
))
g
    Lam ("ds"
   App (
      Lam ("wild"
         Case (
            Var ds (TyConApp "Y" [])
            (Alt (DC ("DEFAULT",0,TyBottom,[]),[]),
               Var C (TyConApp "X" []))
            (Alt (DC ("G",1,TyConApp "Y" [],[]),[]),
               Var B (TyConApp "X" []))
 TyConApp "X" []) TyFun (
         TyConApp "Y" []
         TyConApp "X" []
      ))
      Var ds (TyConApp "Y" [])
   ) TyFun (
   TyConApp "Y" []
   TyConApp "X" []
))
intToInt
    Lam ("x"
   App (
      App (
         App (
            App (
               Var + (TyForAll "a"(TyFun (
                        TyConApp "Num" [ TyVar "a"]
                        TyFun ( TyVar "a"
                           TyFun ( TyVar "a" TyVar "a"
                           )
                        )
                     )))
               Type (TyConApp "Int" [])
            )
            Var $fNumInt (TyConApp "Num" [TyConApp "Int" []])
         )
         Var x (TyConApp "Int" [])
      )
      App (
         Var I# (TyFun ( TyRawInt
               TyConApp "Int" []
            ))
         Const (CInt 3)
      )
   ) TyFun (
   TyConApp "Int" []
   TyConApp "Int" []
))
wild
    Var dsd (TyConApp "X" [])
wild1
    Var ds1d (TyConApp "Y" [])
xApp
    App (
   Var D (TyFun (
         TyConApp "applyType" []
         TyConApp "X" []
      ))
   Var applyCon (TyAlg "applyType" [])
)
xApp2
    App (
   App (
      Var E (TyFun (
            TyConApp "applyType" []
            TyFun (
               TyConApp "applyType" []
               TyConApp "X" []
            )
         ))
      Var applyCon (TyAlg "applyType" [])
   )
   Var applyCon (TyAlg "applyType" [])
)

> Curr Expr:
Var B (TyConApp "X" [])

> Path Constraints:
Var ds1d (TyConApp "Y" []) != Alt (DC ("G",1,TyConApp "Y" [],[]),[])
--AND--
Var dsd (TyConApp "X" []) = Alt (DC ("A",1,TyConApp "X" [],[TyConApp "Y" []]),["ds1d"])
Compiles!
Sat
dsd -> B

Sat
dsd -> C

