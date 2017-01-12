module G2.Sample.Prog1 where

import G2.Core.Language
import G2.Core.Models

import qualified Data.Map as M

leaf = ("Leaf", 1, [TyConApp "Int" []])
node = ("Node", 2, [TyConApp "Tree" [], TyConApp "Tree" []])

t_decls = [("Tree", [leaf, node])]
t_env = M.fromList t_decls

simple_btree_1 = App (App (DCon node)
                          (App (DCon leaf) (Const (CInt 1))))
                     (App (DCon leaf) (Const (CInt 2)))

simple_btree_2 = App (DCon leaf) (Const (CInt 3))

comp_tree = App (App (DCon node) simple_btree_1) simple_btree_2

mkbtree a b c = App (App (DCon node)
                         (App (App (DCon node)
                                   (App (DCon leaf) a))
                              (App (DCon leaf) b)))
                    (App (DCon leaf) c)

test1 = (Case (mkbtree (Var "a") (Var "b") (Var "c"))
              [((node, ["a", "b"]),
                      Case (Var "a")
                           [((node, ["a", "b"]), Var "a")
                           ,((leaf, ["a"]), Var "a")])
              ,((leaf, ["a"]), Var "a")])

test2 = Case (App (App (Var "a") (Var "b")) (Var "c"))
             [((node, ["a", "b"]), Var "a")
             ,((leaf, ["a"]), Var "a")]

e_decls = [("test1", test1)
          ,("test2", test2)]
e_env = M.fromList e_decls

