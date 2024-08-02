{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}

-- | An environemnt for tracking Mutable Variables.
module G2.Language.MutVarEnv where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import GHC.Generics (Generic)
import Data.Data (Data, Typeable)

-- Note [MutVar Env]
-- Mutable variables are variables with values that can be changed. These variables are represented via the `MutVar Name`
-- constructor of `Primitive`. The `Name` of a mutable variable is constant.  A `MutVarEnv maps each (constant) mutable
-- variable name `n` to an `Id` `i`.  The expression returned by `E.lookup (idName i) (expr_env s)` is then the current
-- value of the mutable variable `n`.
--
-- To update the value of a mutable variable `n` to a new expression `e`, we create a fresh `Id` `i'`, and map `i'` to `e` in a
-- `State`'s expression environment.  Then, we update the `mutvar_env` so that `n` maps to `i'`.

-- | Records whether a MutVar was created via newMutVar# or concretization.
data MVOrigin = MVSymbolic -- ^ A MutVar concretized from a symbolic variable.
              | MVConc -- ^ A MutVar created via the newMutVar# function.
              deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable MVOrigin

-- | Information about a `MutVar`.
data MVInfo = MVInfo { mv_val_id :: Id -- ^ The value of the MutVar.  Can be looked up by `Name` in `ExprEnv`. 
                     , mv_initial :: Id -- ^ The initial value of the MutVar i.e. the value of the MutVar when it was created.
                     , mv_origin :: MVOrigin -- ^ Was the MutVar generated from a symbolic variable or from a concrete call to `newMutVar#`?
                     }
                     deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable MVInfo

-- | MutVar `Name`s to mappings of names in the `ExprEnv`. 
-- See Note [MutVar Env].
type MutVarEnv = HM.HashMap Name MVInfo

-- Initalizes a new MutVar in the `MutVarEnv`.
insertMvVal :: Name -> Id -> MVOrigin -> MutVarEnv -> MutVarEnv
insertMvVal n i org = HM.insert n (MVInfo { mv_val_id = i, mv_initial = i, mv_origin = org })

-- | Update the value of a MutVar.  Has no effect if the passed `Name` is not in the `MutVarEnv`.
updateMvVal :: Name -> Id -> MutVarEnv -> MutVarEnv
updateMvVal n i = HM.adjust (\mvi -> mvi { mv_val_id = i }) n

lookupMvVal :: Name -> MutVarEnv -> Maybe Id
lookupMvVal n = fmap mv_val_id . HM.lookup n

instance Named MVInfo where
    names mvi = names (mv_val_id mvi) <> names (mv_initial mvi)
    rename old new mvi = MVInfo { mv_val_id = rename old new (mv_val_id mvi) 
                                , mv_initial = rename old new (mv_initial mvi)
                                , mv_origin = mv_origin mvi }
    renames hm mvi = MVInfo { mv_val_id = renames hm (mv_val_id mvi) 
                            , mv_initial = renames hm (mv_initial mvi)
                            , mv_origin = mv_origin mvi }

instance ASTContainer MVInfo Expr where
    containedASTs _ = []
    modifyContainedASTs _ mvi = mvi

instance ASTContainer MVInfo Type where
    containedASTs (MVInfo { mv_val_id = i }) = containedASTs i
    modifyContainedASTs f (MVInfo { mv_val_id = i, mv_initial = initial, mv_origin = org }) =
            MVInfo { mv_val_id = modifyContainedASTs f i, mv_initial = modifyContainedASTs f initial, mv_origin = org }