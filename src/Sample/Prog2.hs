module G2.Sample.Prog2 where

import G2.Core.Language

import qualified Data.Map as M

ty_tree = TyConApp "Tree" []
leaf = ("Leaf", 1, ty_tree, [TyInt])
node = ("Node", 2, ty_tree, [ty_tree, ty_tree])

{-
  data Tree = Leaf Int | Node Tree Tree
-}

t_decls = [("Tree", TyAlg "Tree" [leaf, node])]

t_env = M.fromList t_decls

join a b = App (App (DCon node ty_tree) a) b

intLeaf a = App (DCon leaf ty_tree) (Const (CInt a) TyInt)

varLeaf a = App (DCon leaf ty_tree) (Var a TyInt)

tree_1 = join (join (varLeaf "a") (varLeaf "b")) (varLeaf "c")

{-
  tree_1 = Node (Node "a" "b") "c"
-}

inner = Case tree_1
             [((leaf, ["a"]), tree_1)
             ,((node, ["a", "b"]), Var "a" ty_tree)]
             ty_tree

{-
  inner = case tree_1 of
      Leaf a   -> tree_1
      Node a b -> a
-}

outer = Case inner
             [((leaf, ["a"]), inner)
             ,((node, ["a", "b"]), Var "b" ty_tree)]
             ty_tree

{-
  outer = case inner of
      Leaf a   -> inner
      NOde a b -> b
-}

ty_foo_1 = TyFun TyInt TyInt
ty_foo_2 = TyFun ty_tree ty_foo_1
ty_foo_3 = TyFun TyInt ty_foo_2

ty_foo_n = TyFun TyInt (TyFun ty_tree (TyFun TyInt TyInt))
foo = Lam "inner"
          (Lam "outer"
              (Lam "foo"
                   (Const (CInt 9999) TyInt)
                   ty_foo_1)
              ty_foo_2)
          ty_foo_3

{-
  foo (a :: Int) (b :: Tree) (c:: Int) = 9999
-}

test = App (App (App (Var "foo" ty_foo_3)
                     (Const (CInt 123) TyInt))
                (Var "outer" ty_tree))
           (Const (CInt 456) TyInt)

{-
  test = foo 123 outer 456
-}

e_decls = [("inner", inner)
          ,("outer", outer)
          ,("test", test)]

e_env = M.fromList e_decls
