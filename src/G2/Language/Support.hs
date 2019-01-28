{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module G2.Language.Support
    ( module G2.Language.AST
    , module G2.Language.Support
    , module G2.Language.TypeEnv
    , AT.ApplyTypes
    , E.ExprEnv
    , PathConds
    , KnownValues
    , PathCond (..)
    , Constraint
    , Assertion
    ) where

import qualified G2.Language.ApplyTypes as AT
import G2.Language.AST
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.Naming
import G2.Language.Stack
import G2.Language.Syntax
import G2.Language.TypeClasses
import G2.Language.TypeEnv
import G2.Language.PathConds hiding (map, filter)
import G2.Execution.RuleTypes

import qualified Data.Map as M
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import qualified Data.Text as T

-- | The State is passed around in G2. It can be utilized to
-- perform defunctionalization, execution, and SMT solving.
-- The t parameter can be used to track extra information during the execution.
data State t = State { expr_env :: E.ExprEnv
                     , type_env :: TypeEnv
                     , curr_expr :: CurrExpr
                     , name_gen :: NameGen
                     , path_conds :: PathConds -- ^ Path conditions, in SWHNF
                     , non_red_path_conds :: [Expr] -- ^ Path conditions that still need further reduction
                     , true_assert :: Bool -- ^ Have we violated an assertion?
                     , assert_ids :: Maybe FuncCall
                     , type_classes :: TypeClasses
                     , symbolic_ids :: SymbolicIds
                     , exec_stack :: Stack Frame
                     , model :: Model
                     , known_values :: KnownValues
                     , rules :: ![Rule]
                     , num_steps :: !Int -- Invariant: The length of the rules list
                     , tags :: S.HashSet Name -- ^ Allows attaching tags to a State, to identify it later
                     , track :: t
                     } deriving (Show, Eq, Read)

data Bindings = Bindings { deepseq_walkers :: Walkers
                         , fixed_inputs :: [Expr]
                         , arb_value_gen :: ArbValueGen 
                         , cleaned_names :: CleanedNames
                         , func_table :: FuncInterps
                         , apply_types :: AT.ApplyTypes
                         , input_ids :: InputIds
                         } deriving (Show, Eq, Read)

-- | The `InputIds` are a list of the variable names passed as input to the
-- function being symbolically executed
type InputIds = [Id]

-- | The `SymbolicIds` are a list of the variable names that we should ensure are
-- inserted in the model, after we solve the path constraints
type SymbolicIds = [Id]

-- | `CurrExpr` is the current expression we have. 
data CurrExpr = CurrExpr EvalOrReturn Expr
              deriving (Show, Eq, Read)

-- | Tracks whether the `CurrExpr` is being evaluated, or if
-- it is in some terminal form that is simply returned. Technically we do not
-- need to make this distinction, and could simply call a `isTerm` function
-- to check, but this makes clearer distinctions for writing the
-- evaluation code.
data EvalOrReturn = Evaluate
                  | Return
                  deriving (Show, Eq, Read)


-- | Function interpretation table.
-- Maps ADT constructors representing functions to their interpretations.
newtype FuncInterps = FuncInterps (M.Map Name (Name, Interp))
                    deriving (Show, Eq, Read)

-- | Functions can have a standard interpretation or be uninterpreted.
data Interp = StdInterp | UnInterp deriving (Show, Eq, Read)

-- Used to map names (typically of ADTs) to corresponding autogenerated function names
type Walkers = M.Map Name Id

-- Map new names to old ones
type CleanedNames = HM.HashMap Name Name

data ArbValueGen = ArbValueGen { intGen :: Integer
                               , floatGen :: Rational
                               , doubleGen :: Rational
                               , boolGen :: Bool
                               } deriving (Show, Eq, Read)

-- | Naive expression lookup by only the occurrence name string.
naiveLookup :: T.Text -> E.ExprEnv -> [(Name, Expr)]
naiveLookup key = filter (\(Name occ _ _ _, _) -> occ == key) . E.toExprList

emptyFuncInterps :: FuncInterps
emptyFuncInterps = FuncInterps M.empty

-- | Do some lookups into the function interpretation table.
lookupFuncInterps :: Name -> FuncInterps -> Maybe (Name, Interp)
lookupFuncInterps name (FuncInterps fs) = M.lookup name fs

-- | Add some items into the function interpretation table.
insertFuncInterps :: Name -> (Name, Interp) -> FuncInterps -> FuncInterps
insertFuncInterps fun int (FuncInterps fs) = FuncInterps (M.insert fun int fs)

-- | These are stack frames.  They are used to guide evaluation.
data Frame = CaseFrame Id [Alt]
           | ApplyFrame Expr
           | UpdateFrame Name
           | CastFrame Coercion
           | CurrExprFrame CurrExpr
           | AssumeFrame Expr
           | AssertFrame (Maybe FuncCall) Expr
           deriving (Show, Eq, Read)

-- | A model is a mapping of symbolic variable names to `Expr`@s@,
-- typically produced by a solver. 
type Model = M.Map Name Expr

-- | Replaces all of the names old in state with a name seeded by new_seed
renameState :: Named t => Name -> Name -> State t -> State t
renameState old new_seed s =
    let (new, ng') = freshSeededName new_seed (name_gen s)
    in State { expr_env = rename old new (expr_env s)
             , type_env =
                  M.mapKeys (\k -> if k == old then new else k)
                  $ rename old new (type_env s)
             , curr_expr = rename old new (curr_expr s)
             , name_gen = ng'
             , path_conds = rename old new (path_conds s)
             , non_red_path_conds = rename old new (non_red_path_conds s)
             , true_assert = true_assert s
             , assert_ids = rename old new (assert_ids s)
             , type_classes = rename old new (type_classes s)
             , symbolic_ids = rename old new (symbolic_ids s)
             , exec_stack = exec_stack s
             , model = model s
             , known_values = rename old new (known_values s)
             , rules = rules s
             , num_steps = num_steps s
             , track = rename old new (track s)
             , tags = tags s }

instance Named t => Named (State t) where
    names s = names (expr_env s)
            ++ names (type_env s)
            ++ names (curr_expr s)
            ++ names (path_conds s)
            ++ names (assert_ids s)
            ++ names (type_classes s)
            ++ names (symbolic_ids s)
            ++ names (exec_stack s)
            ++ names (model s)
            ++ names (known_values s)
            ++ names (track s)

    rename old new s =
        State { expr_env = rename old new (expr_env s)
               , type_env =
                    M.mapKeys (\k -> if k == old then new else k)
                    $ rename old new (type_env s)
               , curr_expr = rename old new (curr_expr s)
               , name_gen = name_gen s
               , path_conds = rename old new (path_conds s)
               , non_red_path_conds = rename old new (non_red_path_conds s)
               , true_assert = true_assert s
               , assert_ids = rename old new (assert_ids s)
               , type_classes = rename old new (type_classes s)
               , symbolic_ids = rename old new (symbolic_ids s)
               , exec_stack = rename old new (exec_stack s)
               , model = rename old new (model s)
               , known_values = rename old new (known_values s)
               , rules = rules s
               , num_steps = num_steps s
               , track = rename old new (track s)
               , tags = tags s }

    renames hm s =
        State { expr_env = renames hm (expr_env s)
               , type_env =
                    M.mapKeys (renames hm)
                    $ renames hm (type_env s)
               , curr_expr = renames hm (curr_expr s)
               , name_gen = name_gen s
               , path_conds = renames hm (path_conds s)
               , non_red_path_conds = renames hm (non_red_path_conds s)
               , true_assert = true_assert s
               , assert_ids = renames hm (assert_ids s)
               , type_classes = renames hm (type_classes s)
               , symbolic_ids = renames hm (symbolic_ids s)
               , exec_stack = renames hm (exec_stack s)
               , model = renames hm (model s)
               , known_values = renames hm (known_values s)
               , rules = rules s
               , num_steps = num_steps s
               , track = renames hm (track s)
               , tags = tags s }

instance ASTContainer t Expr => ASTContainer (State t) Expr where
    containedASTs s = (containedASTs $ type_env s) ++
                      (containedASTs $ expr_env s) ++
                      (containedASTs $ curr_expr s) ++
                      (containedASTs $ path_conds s) ++
                      (containedASTs $ assert_ids s) ++
                      (containedASTs $ symbolic_ids s) ++
                      (containedASTs $ exec_stack s) ++
                      (containedASTs $ track s)

    modifyContainedASTs f s = s { type_env  = modifyContainedASTs f $ type_env s
                                , expr_env  = modifyContainedASTs f $ expr_env s
                                , curr_expr = modifyContainedASTs f $ curr_expr s
                                , path_conds = modifyContainedASTs f $ path_conds s
                                , assert_ids = modifyContainedASTs f $ assert_ids s
                                , symbolic_ids = modifyContainedASTs f $ symbolic_ids s
                                , exec_stack = modifyContainedASTs f $ exec_stack s
                                , track = modifyContainedASTs f $ track s }

instance ASTContainer t Type => ASTContainer (State t) Type where
    containedASTs s = ((containedASTs . expr_env) s) ++
                      ((containedASTs . type_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      ((containedASTs . assert_ids) s) ++
                      ((containedASTs . type_classes) s) ++
                      ((containedASTs . symbolic_ids) s) ++
                      ((containedASTs . exec_stack) s) ++
                      (containedASTs $ track s)

    modifyContainedASTs f s = s { type_env  = (modifyContainedASTs f . type_env) s
                                , expr_env  = (modifyContainedASTs f . expr_env) s
                                , curr_expr = (modifyContainedASTs f . curr_expr) s
                                , path_conds = (modifyContainedASTs f . path_conds) s
                                , assert_ids = (modifyContainedASTs f . assert_ids) s
                                , type_classes = (modifyContainedASTs f . type_classes) s
                                , symbolic_ids = (modifyContainedASTs f . symbolic_ids) s
                                , exec_stack = (modifyContainedASTs f . exec_stack) s
                                , track = modifyContainedASTs f $ track s }

instance Named Bindings where
    names b = names (fixed_inputs b)
            ++ names (deepseq_walkers b)
            ++ names (cleaned_names b)
            ++ names (func_table b)
            ++ names (apply_types b)
            ++ names (input_ids b)

    rename old new b =
        Bindings { fixed_inputs = rename old new (fixed_inputs b)
                 , deepseq_walkers = rename old new (deepseq_walkers b)
                 , arb_value_gen = arb_value_gen b
                 , cleaned_names = HM.insert new old (cleaned_names b)
                 , func_table = rename old new (func_table b)
                 , apply_types = rename old new (apply_types b)
                 , input_ids = rename old new (input_ids b)
                 }

    renames hm b =
        Bindings { fixed_inputs = renames hm (fixed_inputs b)
               , deepseq_walkers = renames hm (deepseq_walkers b)
               , arb_value_gen = arb_value_gen b
               , cleaned_names = foldr (\(old, new) -> HM.insert new old) (cleaned_names b) (HM.toList hm)
               , func_table = renames hm (func_table b)
               , apply_types = renames hm (apply_types b)
               , input_ids = renames hm (input_ids b)
               }

instance ASTContainer Bindings Expr where
    containedASTs b = (containedASTs $ fixed_inputs b) ++ (containedASTs $ input_ids b)

    modifyContainedASTs f b = b { fixed_inputs = modifyContainedASTs f $ fixed_inputs b
                                , input_ids = modifyContainedASTs f $ input_ids b }

instance ASTContainer Bindings Type where
    containedASTs b = ((containedASTs . fixed_inputs) b) ++ ((containedASTs . input_ids) b)

    modifyContainedASTs f b = b { fixed_inputs = (modifyContainedASTs f . fixed_inputs) b
                                , input_ids = (modifyContainedASTs f . input_ids) b }

instance ASTContainer CurrExpr Expr where
    containedASTs (CurrExpr _ e) = [e]
    modifyContainedASTs f (CurrExpr er e) = CurrExpr er (f e)

instance ASTContainer CurrExpr Type where
    containedASTs (CurrExpr _ e) = containedASTs e
    modifyContainedASTs f (CurrExpr er e) = CurrExpr er (modifyContainedASTs f e)

instance ASTContainer Frame Expr where
    containedASTs (CaseFrame _ a) = containedASTs a
    containedASTs (ApplyFrame e) = [e]
    containedASTs (CurrExprFrame e) = containedASTs e
    containedASTs (AssumeFrame e) = [e]
    containedASTs (AssertFrame _ e) = [e]
    containedASTs _ = []

    modifyContainedASTs f (CaseFrame i a) = CaseFrame i (modifyContainedASTs f a)
    modifyContainedASTs f (ApplyFrame e) = ApplyFrame (f e)
    modifyContainedASTs f (CurrExprFrame e) = CurrExprFrame (modifyContainedASTs f e)
    modifyContainedASTs f (AssumeFrame e) = AssumeFrame (f e)
    modifyContainedASTs f (AssertFrame is e) = AssertFrame is (f e)
    modifyContainedASTs _ fr = fr

instance ASTContainer Frame Type where
    containedASTs (CaseFrame i a) = containedASTs i ++ containedASTs a
    containedASTs (ApplyFrame e) = containedASTs e
    containedASTs (CurrExprFrame e) = containedASTs e
    containedASTs (AssumeFrame e) = containedASTs e
    containedASTs (AssertFrame _ e) = containedASTs e
    containedASTs _ = []

    modifyContainedASTs f (CaseFrame i a) =
        CaseFrame (modifyContainedASTs f i) (modifyContainedASTs f a)
    modifyContainedASTs f (ApplyFrame e) = ApplyFrame (modifyContainedASTs f e)
    modifyContainedASTs f (CurrExprFrame e) = CurrExprFrame (modifyContainedASTs f e)
    modifyContainedASTs f (AssumeFrame e) = AssumeFrame (modifyContainedASTs f e)
    modifyContainedASTs f (AssertFrame is e) = AssertFrame (modifyContainedASTs f is) (modifyContainedASTs f e)
    modifyContainedASTs _ fr = fr

instance Named CurrExpr where
    names (CurrExpr _ e) = names e
    rename old new (CurrExpr er e) = CurrExpr er $ rename old new e
    renames hm (CurrExpr er e) = CurrExpr er $ renames hm e

instance Named FuncInterps where
    names (FuncInterps m) = M.keys m ++ (map fst $ M.elems m) 

    rename old new (FuncInterps m) =
        FuncInterps . M.mapKeys (rename old new) . M.map (\(n, i) -> (rename old new n, i)) $ m

    renames hm (FuncInterps m) =
        FuncInterps . M.mapKeys (renames hm) . M.map (\(n, i) -> (renames hm n, i)) $ m

instance Named Frame where
    names (CaseFrame i a) = names i ++ names a
    names (ApplyFrame e) = names e
    names (UpdateFrame n) = [n]
    names (CastFrame c) = names c
    names (CurrExprFrame e) = names e
    names (AssumeFrame e) = names e
    names (AssertFrame is e) = names is ++ names e

    rename old new (CaseFrame i a) = CaseFrame (rename old new i) (rename old new a)
    rename old new (ApplyFrame e) = ApplyFrame (rename old new e)
    rename old new (UpdateFrame n) = UpdateFrame (rename old new n)
    rename old new (CastFrame c) = CastFrame (rename old new c)
    rename old new (CurrExprFrame e) = CurrExprFrame (rename old new e)
    rename old new (AssumeFrame e) = AssumeFrame (rename old new e)
    rename old new (AssertFrame is e) = AssertFrame (rename old new is) (rename old new e)

    renames hm (CaseFrame i a) = CaseFrame (renames hm i) (renames hm a)
    renames hm (ApplyFrame e) = ApplyFrame (renames hm e)
    renames hm (UpdateFrame n) = UpdateFrame (renames hm n)
    renames hm (CastFrame c) = CastFrame (renames hm c)
    renames hm (CurrExprFrame e) = CurrExprFrame (renames hm e)
    renames hm (AssumeFrame e) = AssumeFrame (renames hm e)
    renames hm (AssertFrame is e) = AssertFrame (renames hm is) (renames hm e)
