module G2.Internals.SMT.Converters where

import G2.Internals.Core.Language hiding (Assert)
import G2.Internals.SMT.Language

-- | toSMT
-- Here we convert from a State, to an SMTHeader.  This SMTHeader can later
-- be given to an SMT solver by using toSolver.
-- To determine the input that can be fed to a state to get the curr_expr,
-- we need only consider the types and path constraints of that state.
-- Of course, we can also solve for the curr_expr, to also get the output.
toSMT :: State -> [SMTHeader]
toSMT s = 
	   map typesToSMTSorts $ type_env s
	++ map pathConsToSMT $ path_cons s

pathConsToSMT :: PathCond -> SMTHeader
pathConsToSMT (CondAlt e a b) =
	let
		exprSMT = exprToSMT e
		altSMT = altToSMT a
	in
	Assert $ if b then exprSMT := altSMT else (:!) (exprSMT := altSMT) 
toSMTPathCons (CondExt e b) =
	let
		exprSMT = exprToSMT e
	in
	Assert $ if b then exprSMT else (:!) exprSMT 

exprToSMT :: Expr -> SMTAST



toSolver :: SMTConverter ast out -> [SMTHeader] -> out
toSolver con [] = empty con
toSolver con (Assert ast:xs) = merge con (assert con $ toSolverAST con ast) (toSolver con xs)
toSolver con (SortDecl ns:xs) = merge con (toSolverSortDecl con ns) (toSolver con xs)

toSolverAST :: SMTConverter ast out -> SMTAST -> ast
toSolverAST con (x :>= y) = (.>=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :> y) = (.>) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x := y) = (.=) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :< y) = (.<) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :<= y) = (.<=) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :&& y) = (.&&) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :|| y) =  (.||) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con ((:!) x) = (.!) con $ toSolverAST con x
toSolverAST con (x :=> y) = (.=>) con (toSolverAST con x) (toSolverAST con y)

toSolverAST con (x :+ y) = (.+) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :- y) = (.-) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :* y) = (.*) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (x :/ y) = (./) con (toSolverAST con x) (toSolverAST con y)
toSolverAST con (Neg x) = neg con $ toSolverAST con x

toSolverAST con (Ite x y z) =
    ite con (toSolverAST con x) (toSolverAST con y) (toSolverAST con z)

toSolverAST con (VInt i) = int con i
toSolverAST con (VFloat f) = float con f
toSolverAST con (VDouble i) = double con i
toSolverAST con (VBool b) = bool con b

toSolverSortDecl :: SMTConverter ast out -> [(Name, [Sort])] -> out
toSolverSortDecl con [] = empty con

toSolverSort :: SMTConverter ast out -> Sort -> ast
toSolverSort con SortInt = sortInt con
toSolverSort con SortFloat = sortFloat con
toSolverSort con SortDouble = sortDouble con
toSolverSort con SortBool = sortBool con
toSolverSort con (Sort n) = sortName con n