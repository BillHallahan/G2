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

-- DCPCMap :: HM.HashMap (DataCon, [Type]) DataConPCInfo
-- DCPCMap = HM.fromList [
--             ((), strDcpc),
--             ((), strEmptyDcpc)
--         ]

applyDCPC :: NameGen
          -> ExprEnv
          -> [Id] -- ^ Newly generated arguments for the data constructor
          -> Name -- ^ As pattern name to replace
          -> DataConPCInfo
          -> (ExprEnv, [PathCond], NameGen)
applyDCPC ng eenv new_ids prev_asp (DCPC { dc_id = did, dc_as_pattern = asp, dc_args = ars, dc_pc = pc }) =
    let
        (ng', eenv', pc') = foldl' mkDCArg (ng, eenv, pc) (zip ars new_ids)
        pc'' = rename asp prev_asp pc'
    in
    assert (length ars == length new_ids)
    (eenv', pc'', ng')


mkDCArg :: (NameGen, ExprEnv, [PathCond]) -> (DCArgBind, Id) -> (NameGen, ExprEnv, [PathCond])
mkDCArg (ng, eenv, pc) (ArgSymb bi, i) =
    let
        eenv' = E.insertSymbolic i eenv
        pc' = rename bi (idName i) pc
    in
    (ng, eenv', pc')
mkDCArg (ng, eenv, pc) (ArgConcretize { binder_name = bn, fresh_vars = fv, arg_expr = e}, i) =
    let
        (fv', ng') = freshSeededIds fv ng
        rn_hm = HM.fromList $ (bn, idName i):zip (map idName fv) (map idName fv')
        e' = renames rn_hm e
        pc' = renames rn_hm pc
        eenv' = E.insert (idName i) e' $ foldl' (flip E.insertSymbolic) eenv fv'
    in
    (ng', eenv', pc')
