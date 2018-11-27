module OkasakiRedBlack where

data Color = R | B
data Tree elt = E | T Color (Tree elt) elt (Tree elt)

insert :: Ord elt => elt -> Tree elt -> Tree elt
insert x s = makeBlack (ins x s)

ins :: Ord elt => elt -> Tree elt -> Tree elt
ins x E = T R E x E
ins x (T color a y b)
    | x < y = balance color (ins x a) y b
    | x == y = T color a y b
    | x > y = balance color a y (ins x b)

makeBlack (T _ a y b) = T B a y b

balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance color a x b = T color a x b
