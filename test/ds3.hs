module DataTypes where

data X = A | B | C X

f :: X -> X
f A = B
f B = A
f (C x) =
    case x of
        A -> B
        B -> B
        C B -> C A
        C A -> C B
        otherwise -> A

g :: X -> X
g A = A
g B = B
g (C x) = C (g x)
