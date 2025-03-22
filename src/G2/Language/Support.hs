{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric#-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}

module G2.Language.Support
    ( module G2.Language.AST
    , module G2.Language.Support
    , module G2.Language.TypeEnv
    , E.ExprEnv
    , PathConds
    , KnownValues
    , PathCond (..)
    , Constraint
    , Assertion
    ) where

import G2.Language.AST
import qualified G2.Language.ExprEnv as E
import G2.Language.KnownValues
import G2.Language.MutVarEnv
import G2.Language.Naming
import G2.Language.Stack hiding (filter)
import G2.Language.Syntax
import G2.Language.TypeClasses
import G2.Language.TypeEnv
import G2.Language.Typing
import G2.Language.PathConds hiding (map, filter)
import G2.Execution.RuleTypes

import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Hashable
import qualified Data.Map as M
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import qualified Data.Sequence as S

-- | `State`s represent an execution state of some (symbolic) Haskell code.
-- A state can be utilized to  perform execution and SMT solving.
-- The t parameter can be used to track extra information during the execution.
data State t = State { expr_env :: E.ExprEnv -- ^ Mapping of `Name`s to `Expr`s
                     , type_env :: TypeEnv -- ^ Type information
                     , curr_expr :: CurrExpr -- ^ The expression represented by the state
                     , path_conds :: PathConds -- ^ Path conditions, in SWHNF
                     , non_red_path_conds :: [(Expr, Expr)] -- ^ Path conditions, in the form of (possibly non-reduced)
                                                            -- expression pairs that must be proved equivalent
                     , handles :: HM.HashMap Name Handle -- ^ Each Handle has a name, that appears in `Expr`s within the `Handle` `Primitive`
                     , mutvar_env :: MutVarEnv -- ^ MutVar `Name`s to mappings of names in the `ExprEnv`.
                                               -- See Note [MutVar Env] in G2.Language.MutVarEnv.
                     , true_assert :: Bool -- ^ Do we want to output the state?  True if yes, false if no.
                                           -- When running to violate assertions, an assertion violations flips this from False to True.
                     , assert_ids :: Maybe FuncCall
                     , type_classes :: TypeClasses
                     , exec_stack :: Stack Frame
                     , model :: Model
                     , known_values :: KnownValues
                     , rules :: ![Rule]
                     , num_steps :: !Int -- Invariant: The length of the rules list
                     , tags :: S.HashSet Name -- ^ Allows attaching tags to a State, to identify it later
                     , sym_gens :: S.Seq Name -- ^ Variable names generated by logging `SymGen`s
                     , track :: t
                     } deriving (Show, Eq, Read, Generic, Typeable, Data)


instance Hashable t => Hashable (State t)

-- | Global information, shared between all `State`s.
data Bindings = Bindings { fixed_inputs :: [Expr]
                         , arb_value_gen :: ArbValueGen 
                         , cleaned_names :: CleanedNames
                         , higher_order_inst :: S.HashSet Name -- ^ Functions to try instantiating higher order functions with

                         , input_names :: [Name] -- ^ Names of input symbolic arguments
                         , input_coercion :: Maybe Coercion -- ^ Coercion wrapping the initial function call
                         
                         , rewrite_rules :: ![RewriteRule]
                         , name_gen :: NameGen
                         , exported_funcs :: [Name]
                         } deriving (Show, Eq, Read, Typeable, Data)

-- | The `InputIds` are a list of the variable names passed as input to the
-- function being symbolically executed
type InputIds = [Id]

inputIds :: State t -> Bindings -> InputIds
inputIds (State { expr_env = eenv }) (Bindings { input_names = ns }) =
    map (\n -> case E.lookup n eenv of
                Just e -> Id n (typeOf e)
                Nothing -> error "inputIds: Name not found in ExprEnv") ns

-- | `CurrExpr` is the current expression we have. 
data CurrExpr = CurrExpr EvalOrReturn Expr
              deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable CurrExpr

-- | Gets the `Expr` represented by a state.
getExpr :: State t -> Expr
getExpr (State { curr_expr = CurrExpr _ e }) = e

-- | Tracks whether the `CurrExpr` is being evaluated, or if
-- it is in some terminal form that is simply returned. Technically we do not
-- need to make this distinction, and could simply call a `isTerm` function
-- to check, but this makes clearer distinctions for writing the
-- evaluation code.
data EvalOrReturn = Evaluate
                  | Return
                  deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable EvalOrReturn

-- Map new names to old ones
type CleanedNames = HM.HashMap Name Name

data ArbValueGen = ArbValueGen { intGen :: Integer
                               , floatGen :: Float
                               , doubleGen :: Double
                               , rationalGen :: Rational
                               , charGen :: [Char]
                               , boolGen :: Bool
                               } deriving (Show, Eq, Read, Typeable, Data)

-- | These are stack frames that are used to guide evaluation.
data Frame = CaseFrame Id Type [Alt]
           | ApplyFrame Expr
           | UpdateFrame Name
           | CastFrame Coercion
           | CurrExprFrame CEAction CurrExpr
           | AssumeFrame Expr
           | AssertFrame (Maybe FuncCall) Expr
           deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Frame

-- | What to do with the current expression when a @CurrExprFrame@ reaches the
-- top of the stack and it is time to replace the `curr_expr`.
data CEAction = EnsureEq Expr -- ^ `EnsureEq e1` means that we should check if the `curr_expr` is equal to `e1`
              | NoAction -- ^ Just replace the curr_expr, no other actions are needed
              deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable CEAction

-- | A model is a mapping of symbolic variable names to `Expr`@s@,
-- typically produced by a solver. 
type Model = HM.HashMap Name Expr

-- | A highly simplified model of Handles.
data Handle = HandleInfo { h_filepath :: FilePath
                         , h_start :: Id -- ^ The entire contents of the file, maps to a String in the `ExprEnv`
                         , h_pos :: Id -- ^ The current position of the Handle, maps to a String in the `ExprEnv`
                         , h_status :: HandleStatus }
                         deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Handle

data HandleStatus = HOpen | HClosed
                    deriving (Show, Eq, Read, Generic, Typeable, Data)

stdinName :: Name
stdinName = Name "stdin" Nothing 0 Nothing

stdoutName :: Name
stdoutName = Name "stdout" Nothing 0 Nothing

stderrName :: Name
stderrName = Name "stderr" Nothing 0 Nothing

instance Hashable HandleStatus

instance Named t => Named (State t) where
    names s = names (expr_env s)
            <> names (type_env s)
            <> names (curr_expr s)
            <> names (path_conds s)
            <> names (non_red_path_conds s)
            <> names (handles s)
            <> names (mutvar_env s)
            <> names (assert_ids s)
            <> names (type_classes s)
            <> names (exec_stack s)
            <> names (model s)
            <> names (known_values s)
            <> names (track s)
            <> names (sym_gens s)

    rename old new s =
        State { expr_env = rename old new (expr_env s)
               , type_env =
                    HM.mapKeys (\k -> if k == old then new else k)
                    $ rename old new (type_env s)
               , curr_expr = rename old new (curr_expr s)
               , path_conds = rename old new (path_conds s)
               , non_red_path_conds = rename old new (non_red_path_conds s)
               , handles = rename old new (handles s)
               , mutvar_env = rename old new (mutvar_env s)
               , true_assert = true_assert s
               , assert_ids = rename old new (assert_ids s)
               , type_classes = rename old new (type_classes s)
               , exec_stack = rename old new (exec_stack s)
               , model = rename old new (model s)
               , known_values = rename old new (known_values s)
               , rules = rules s
               , num_steps = num_steps s
               , track = rename old new (track s)
               , sym_gens = rename old new (sym_gens s)
               , tags = tags s }

    renames hm s =
        State { expr_env = renames hm (expr_env s)
               , type_env =
                    HM.mapKeys (renames hm)
                    $ renames hm (type_env s)
               , curr_expr = renames hm (curr_expr s)
               , path_conds = renames hm (path_conds s)
               , non_red_path_conds = renames hm (non_red_path_conds s)
               , handles = renames hm (handles s)
               , mutvar_env = renames hm (mutvar_env s)
               , true_assert = true_assert s
               , assert_ids = renames hm (assert_ids s)
               , type_classes = renames hm (type_classes s)
               , exec_stack = renames hm (exec_stack s)
               , model = renames hm (model s)
               , known_values = renames hm (known_values s)
               , rules = rules s
               , num_steps = num_steps s
               , track = renames hm (track s)
               , sym_gens = renames hm (sym_gens s)
               , tags = tags s }

instance ASTContainer t Expr => ASTContainer (State t) Expr where
    containedASTs s = (containedASTs $ type_env s) ++
                      (containedASTs $ expr_env s) ++
                      (containedASTs $ curr_expr s) ++
                      (containedASTs $ path_conds s) ++
                      (containedASTs $ non_red_path_conds s) ++
                      (containedASTs $ handles s) ++
                      (containedASTs $ mutvar_env s) ++
                      (containedASTs $ assert_ids s) ++
                      (containedASTs $ exec_stack s) ++
                      (containedASTs $ track s) ++ 
                      (containedASTs $ sym_gens s) ++
                      (containedASTs $ rules s)

    modifyContainedASTs f s = s { type_env  = modifyContainedASTs f $ type_env s
                                , expr_env  = modifyContainedASTs f $ expr_env s
                                , curr_expr = modifyContainedASTs f $ curr_expr s
                                , path_conds = modifyContainedASTs f $ path_conds s
                                , non_red_path_conds = modifyContainedASTs f $ non_red_path_conds s
                                , handles = modifyContainedASTs f $ handles s
                                , mutvar_env = modifyContainedASTs f $ mutvar_env s
                                , assert_ids = modifyContainedASTs f $ assert_ids s
                                , exec_stack = modifyContainedASTs f $ exec_stack s
                                , track = modifyContainedASTs f $ track s 
                                , sym_gens = modifyContainedASTs f $ sym_gens s 
                                , rules = modifyContainedASTs f $ rules s }

instance ASTContainer t Type => ASTContainer (State t) Type where
    containedASTs s = ((containedASTs . expr_env) s) ++
                      ((containedASTs . type_env) s) ++
                      ((containedASTs . curr_expr) s) ++
                      ((containedASTs . path_conds) s) ++
                      (containedASTs $ non_red_path_conds s) ++
                      (containedASTs $ handles s) ++
                      (containedASTs $ mutvar_env s) ++
                      ((containedASTs . assert_ids) s) ++
                      ((containedASTs . type_classes) s) ++
                      ((containedASTs . exec_stack) s) ++
                      (containedASTs $ track s) ++ 
                      (containedASTs $ sym_gens s) ++
                      (containedASTs $ rules s)

    modifyContainedASTs f s = s { type_env  = (modifyContainedASTs f . type_env) s
                                , expr_env  = (modifyContainedASTs f . expr_env) s
                                , curr_expr = (modifyContainedASTs f . curr_expr) s
                                , path_conds = (modifyContainedASTs f . path_conds) s
                                , non_red_path_conds = modifyContainedASTs f $ non_red_path_conds s
                                , handles = modifyContainedASTs f $ handles s
                                , mutvar_env = modifyContainedASTs f $ mutvar_env s
                                , assert_ids = (modifyContainedASTs f . assert_ids) s
                                , type_classes = (modifyContainedASTs f . type_classes) s
                                , exec_stack = (modifyContainedASTs f . exec_stack) s
                                , track = modifyContainedASTs f $ track s 
                                , sym_gens = modifyContainedASTs f $ sym_gens s 
                                , rules = modifyContainedASTs f $ rules s }

instance Named Bindings where
    names b = names (fixed_inputs b)
            <> names (cleaned_names b)
            <> names (higher_order_inst b)
            <> names (input_names b)
            <> names (input_coercion b)
            <> names (exported_funcs b)
            <> names (rewrite_rules b)

    rename old new b =
        Bindings { fixed_inputs = rename old new (fixed_inputs b)
                 , arb_value_gen = arb_value_gen b
                 , cleaned_names = HM.insert new old (cleaned_names b)
                 , higher_order_inst = rename old new (higher_order_inst b)
                 , input_names = rename old new (input_names b)
                 , input_coercion = rename old new (input_coercion b)
                 , rewrite_rules = rename old new (rewrite_rules b)
                 , name_gen = name_gen b
                 , exported_funcs = rename old new (exported_funcs b)
                 }

    renames hm b =
        Bindings { fixed_inputs = renames hm (fixed_inputs b)
               , arb_value_gen = arb_value_gen b
               , cleaned_names = foldr (\(old, new) -> HM.insert new old) (cleaned_names b) (HM.toList hm)
               , higher_order_inst = renames hm (higher_order_inst b)
               , input_names = renames hm (input_names b)
               , input_coercion = renames hm (input_coercion b)
               , rewrite_rules = renames hm (rewrite_rules b)
               , name_gen = name_gen b
               , exported_funcs = renames hm (exported_funcs b)
               }

instance ASTContainer Bindings Expr where
    containedASTs b = (containedASTs $ fixed_inputs b) ++ (containedASTs $ input_names b)

    modifyContainedASTs f b = b { fixed_inputs = modifyContainedASTs f $ fixed_inputs b
                                , input_names = modifyContainedASTs f $ input_names b }

instance ASTContainer Bindings Type where
    containedASTs b = (containedASTs . fixed_inputs $ b)
                   ++ (containedASTs . input_names $ b)
                   ++ (containedASTs . input_coercion $ b)

    modifyContainedASTs f b = b { fixed_inputs = modifyContainedASTs f . fixed_inputs $ b
                                , input_names = modifyContainedASTs f . input_names $ b
                                , input_coercion = modifyContainedASTs f . input_coercion $ b }

instance ASTContainer CurrExpr Expr where
    containedASTs (CurrExpr _ e) = [e]
    modifyContainedASTs f (CurrExpr er e) = CurrExpr er (f e)

instance ASTContainer CurrExpr Type where
    containedASTs (CurrExpr _ e) = containedASTs e
    modifyContainedASTs f (CurrExpr er e) = CurrExpr er (modifyContainedASTs f e)

instance ASTContainer Frame Expr where
    containedASTs (CaseFrame _ _ a) = containedASTs a
    containedASTs (ApplyFrame e) = [e]
    containedASTs (CurrExprFrame _ e) = containedASTs e
    containedASTs (AssumeFrame e) = [e]
    containedASTs (AssertFrame _ e) = [e]
    containedASTs _ = []

    modifyContainedASTs f (CaseFrame i t a) = CaseFrame i t (modifyContainedASTs f a)
    modifyContainedASTs f (ApplyFrame e) = ApplyFrame (f e)
    modifyContainedASTs f (CurrExprFrame act e) = CurrExprFrame act (modifyContainedASTs f e)
    modifyContainedASTs f (AssumeFrame e) = AssumeFrame (f e)
    modifyContainedASTs f (AssertFrame is e) = AssertFrame is (f e)
    modifyContainedASTs _ fr = fr

instance ASTContainer Frame Type where
    containedASTs (CaseFrame i t a) = containedASTs i ++ containedASTs t ++ containedASTs a
    containedASTs (ApplyFrame e) = containedASTs e
    containedASTs (CurrExprFrame _ e) = containedASTs e
    containedASTs (AssumeFrame e) = containedASTs e
    containedASTs (AssertFrame _ e) = containedASTs e
    containedASTs _ = []

    modifyContainedASTs f (CaseFrame i t a) =
        CaseFrame (modifyContainedASTs f i) (f t) (modifyContainedASTs f a)
    modifyContainedASTs f (ApplyFrame e) = ApplyFrame (modifyContainedASTs f e)
    modifyContainedASTs f (CurrExprFrame act e) = CurrExprFrame act (modifyContainedASTs f e)
    modifyContainedASTs f (AssumeFrame e) = AssumeFrame (modifyContainedASTs f e)
    modifyContainedASTs f (AssertFrame is e) = AssertFrame (modifyContainedASTs f is) (modifyContainedASTs f e)
    modifyContainedASTs _ fr = fr

instance Named CurrExpr where
    names (CurrExpr _ e) = names e
    rename old new (CurrExpr er e) = CurrExpr er $ rename old new e
    renames hm (CurrExpr er e) = CurrExpr er $ renames hm e

instance Named Frame where
    names (CaseFrame i t a) = names i <> names t <> names a
    names (ApplyFrame e) = names e
    names (UpdateFrame n) = names n
    names (CastFrame c) = names c
    names (CurrExprFrame _ e) = names e
    names (AssumeFrame e) = names e
    names (AssertFrame is e) = names is <> names e

    rename old new (CaseFrame i t a) = CaseFrame (rename old new i) (rename old new t) (rename old new a)
    rename old new (ApplyFrame e) = ApplyFrame (rename old new e)
    rename old new (UpdateFrame n) = UpdateFrame (rename old new n)
    rename old new (CastFrame c) = CastFrame (rename old new c)
    rename old new (CurrExprFrame act e) = CurrExprFrame act (rename old new e)
    rename old new (AssumeFrame e) = AssumeFrame (rename old new e)
    rename old new (AssertFrame is e) = AssertFrame (rename old new is) (rename old new e)

    renames hm (CaseFrame i t a) = CaseFrame (renames hm i) (renames hm t) (renames hm a)
    renames hm (ApplyFrame e) = ApplyFrame (renames hm e)
    renames hm (UpdateFrame n) = UpdateFrame (renames hm n)
    renames hm (CastFrame c) = CastFrame (renames hm c)
    renames hm (CurrExprFrame act e) = CurrExprFrame act (renames hm e)
    renames hm (AssumeFrame e) = AssumeFrame (renames hm e)
    renames hm (AssertFrame is e) = AssertFrame (renames hm is) (renames hm e)

instance Named Handle where
    names (HandleInfo { h_start = s, h_pos = p }) = names s <> names p

    rename old new h@(HandleInfo { h_start = s, h_pos = p }) =
        h { h_start = rename old new s, h_pos = rename old new p }

    renames hm h@(HandleInfo { h_start = s, h_pos = p }) =
        h { h_start = renames hm s, h_pos = renames hm p }

instance ASTContainer Handle Expr where
    containedASTs (HandleInfo { h_start = s, h_pos = p }) = containedASTs s <> containedASTs p

    modifyContainedASTs f h@(HandleInfo { h_start = s, h_pos = p }) =
        h { h_start = modifyContainedASTs f s, h_pos = modifyContainedASTs f p }

instance ASTContainer Handle Type where
    containedASTs (HandleInfo { h_start = s, h_pos = p }) = containedASTs s <> containedASTs p

    modifyContainedASTs f h@(HandleInfo { h_start = s, h_pos = p }) =
        h { h_start = modifyContainedASTs f s, h_pos = modifyContainedASTs f p }