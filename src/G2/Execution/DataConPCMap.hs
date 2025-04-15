module G2.Execution.DataConPCMap ( DCArgBind (..)
                                 , DataConPCInfo (..)
                                 , applyDCPC
                                 ) where

import G2.Language.Naming
import qualified G2.Language.PathConds as P
import G2.Language
import qualified G2.Language.ExprEnv as E

import Data.List
import qualified Data.HashMap.Lazy as HM

import Control.Exception

data DCArgBind =
      -- | A new symbolic argument
      ArgSymb { binder_name :: Name }
      -- | A new concrete argument
    | ArgConcretize 
        { binder_name :: Name
        , fresh_vars :: [Id] -- ^ New symbolic variables to introduce, used in the Expr
        , arg_expr :: Expr -- ^ Instantiation of the argument
        }

-- | When adding a data constructor, we can also add path constraints, to enable
-- reasoning via the SMT solver.  For example, Strings can be manipulated via concretization,
-- but also SMT solvers include support for certain String primitives.  So we both concretize
-- (to run arbitrary Haskell functions) but add to the path constraints to enable SMT solver
-- reasoning when possible.
--
-- This type ties specific data constructors to path constraints that should be added during concretization.
-- The path constraints are written over the dc_args, which are either newly introduced symbolic variables
-- or newly introduced concrete values.
data DataConPCInfo =
    DCPC
    { dc_id :: DataCon -- ^ The data constructor that the DCPC applies to
    , dc_as_pattern :: Name -- ^ The entirety of the data constructor application
    , dc_args :: [DCArgBind] -- ^ How to instantiate arguments for the DCPC
    , dc_pc :: [PathCond] -- ^ Path constraints to generate, written over the DCPC
    }

-- mapToDCPC :: DataCon -> TypeEnv -> KnownValues -> Expr -> [Id] -> [Name] -> DataConPCInfo
-- mapToDCPC dc tenv kv mexpr params new_ids 
--     | Just (dcName dc) == fmap dcName (getDataCon tenv (KV.tyList kv) (KV.dcEmpty kv))
--     , typeOf mexpr == TyApp (T.tyList kv) (T.tyChar kv) =

applyDCPC :: NameGen
          -> ExprEnv
          -> [Type]
          -> [Id] -- ^ Newly generated arguments for the data constructor
          -> Name -- ^ As pattern name to replace
          -> DataConPCInfo
          -> (ExprEnv, [PathCond], NameGen)
applyDCPC ng eenv ts new_ids prev_asp (DCPC { dc_id = did, dc_as_pattern = asp, dc_args = ars, dc_pc = pc }) =
    let
        ts' = anonArgumentTypes did 
        ((ng', eenv', pc'), ars_e) = mapAccumL mkDCArg (ng, eenv, pc) $ zip3 ars new_ids ts'
        ars_e' = rename asp prev_asp ars_e
    in
    assert (length ars == length new_ids)
    -- how to insert here without breaking (appTypeOf error ?)
    -- (E.insert prev_asp (mkApp (Data did:map Type ts' ++ ars_e')) eenv', rename asp prev_asp pc', ng')
    (eenv', rename asp prev_asp pc', ng')


mkDCArg :: (NameGen, ExprEnv, [PathCond]) -> (DCArgBind, Id, Type) -> ((NameGen, ExprEnv, [PathCond]), Expr)
mkDCArg (ng, eenv, pc) (ArgSymb bi, i, t) =
    let
        eenv' = E.insertSymbolic i eenv
        pc' = rename bi (idName i) pc
    in
    ((ng, eenv', pc'), Var i)
mkDCArg (ng, eenv, pc) (ArgConcretize { binder_name = bn, fresh_vars = fv, arg_expr = e}, i, _) =
    let
        (fv', ng') = freshSeededIds fv ng
        rn_hm = HM.fromList $ (bn, idName i):zip (map idName fv) (map idName fv')
        e' = renames rn_hm e
        pc' = renames rn_hm pc
        eenv' = E.insert (idName i) e' $ foldl' (flip E.insertSymbolic) eenv fv'
    in
    ((ng', eenv', pc'), e')
