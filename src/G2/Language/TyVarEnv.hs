module TyVarEnv (TyVarEnv, empty, insert, lookup) where 

import Data.Hashable
import qualified Data.HashMap.Lazy as HM

newtype TyVarEnv = TyVarEnv (HM.HashMap Name Type)

empty :: TyVarEnv
empty = TyVarEnv HM.empty

insert :: (Hashable Name, Eq Name) => Name -> Type -> TyVarEnv -> TyVarEnv
insert name ty (TyVarEnv env) = TyVarEnv $ HM.insert name ty env

lookup :: (Hashable Name, Eq Name) => Name -> TyVarEnv -> Maybe Type
lookup name (TyVarEnv env) = HM.lookup name env

