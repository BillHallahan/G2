module G2.Core.Language where

import qualified Data.Map as M

{- Execution State
  
Our execution state consists of 4 things we need to keep track of:
  
1. Type Environment: Contains things such as algebraic data types and
   functions. We primarily need this to reconstruct data during SMT phase.

2. Expression Environment: Maps names (strings) to their corresponding
   expressions. Functions after currying are represented as a sequence of
   cascading lambda expressions.
    
3. Current Expression: The thing we are evaluating.

4. Path Constraint: Keeps track of which alt branching we have taken.
-}
--type State = (TEnv, EEnv, Expr, PC)

data State = State { tEnv  :: TEnv
                   , eEnv  :: EEnv
                   , cExpr :: Expr
                   , pc    :: PC
                   , slt   :: SymLinkTable
                   } deriving (Show, Eq)

type Name = String

type TEnv = M.Map Name Type

type EEnv = M.Map Name Expr

type SymLinkTable = [(Name, Name)]

{- Expressions
  
We annotate our expressions with types. The reason we do this is because we
need type information to reconstruct statements during the SMT phase.

Furthermore, UNR is probably redundant since we can just use BAD instead. If
we choose to remove it, it would just be deleting a few lines.
-}
data Expr = Var Name Type
          | Const Const
          | Lam Name Expr Type
          | App Expr Expr
          | DCon DataCon
          | Case Expr [(Alt, Expr)] Type
          | Type Type
          | BAD
          | UNR
          deriving (Show, Eq)

{- Constants
 
Const reflects Haskell's 4 primitive types: Int, Float, Double, and Char.

We use CString as a way of catching string literals.

We have an additional COp as a way to circumvent Haskell functions such as
plus (+), which operates on boxed (wrapped) numbers, but delegates calls to
plus# (+#), which operates on raw unboxed numbers. As these type of special
case operations are finite, it is better that we don't explicitly try to give
them implementations (as we don't aim to do function evaluation of, say +#),
and instead leave them uninterpreted to report back to the user, or just be
aware of handling them on the SMT phase. Making them Const avoids environment
lookups had they been Var.
-}
data Const = CInt Int
           | CFloat Rational
           | CDouble Rational
           | CChar Char
           | CString String
           | COp Name Type
           deriving (Show, Eq)

{- Data Constructors

Name, tag (possibly will not be used), ADT's type, argument types
-}
newtype DataCon = DC (Name, Int, Type, [Type]) deriving (Show, Eq)

{- Types

Note that the TyRaw types are meant to deal with unboxed types. In our custom
implementation of prelude, we define the "wrapper" ADTs very similar to how
Haskell internally implements things such as:

    data Int = I# Int#

Here, for instance, TyRawInt would be equivalent to Int#.

TyApp is a catch-all statement in case we accidentally run into type vars.

TyConApp is equivalent to applying types to parametrized ADTs:

    data Tree a = Node a | Branch (Tree a) (Tree a)

    foo :: Tree Int -> Int

TyAlg is simply the ADT that lives in the environment. We don't acctually use
the type environment at all during actual symbolic evaluation. However, the
type environment is crucial for reconstruction during SMT phase.
-}
data Type = TyVar Name
          | TyRawInt | TyRawFloat | TyRawDouble | TyRawChar | TyRawString
          | TyFun Type Type
          | TyApp Type Type
          | TyConApp Name [Type]
          | TyAlg Name [DataCon]
          | TyForAll Name Type
          | TyBottom
          deriving (Show, Eq)

{- Alternatives

Matching in case statements is only done on data constructors. This means we
are not able to directly do matching on numbers. However, we are still able
to match on their wrapper data constructors that we define in our prelude.

Here the [Name] refers to the parameters of the data constructor.
-}
newtype Alt = Alt (DataCon, [Name]) deriving (Eq, Show)

{- Path Constraints

Path constraints are expressed as pairs of expressions and the alt expression
that they happened to match on. There are two scenarios that may occur:

  case A b c ... of 
      K1 a1 a2    -> ...
      K2 a1 a2 a3 -> ...

Here two possibilities may happen during symbolic evaluations: either A is a
data constructor whose arguments match to one of the alternatives, or A is
actually an unbonuded variable. If the former is the case, then it would be
straightforward for us to take the corresponding matched branch (if any).
However in the case where A is actually an unbound variable, we must treat
it as a function that returns an ADT, which we will request the SMT to solve
for based on the information it can reconstruct from the tuple.
-}
type PC = [(Expr, Alt, Bool)]

