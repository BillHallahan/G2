{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-}

module G2.Language.TypeAppRenameMap ( TypeAppRenameMap
                               , insert
                               , lookup
                               , member
                               , empty ) where 

import G2.Language.Syntax

import qualified Data.HashMap.Lazy as HM
import Data.Data (Data, Typeable)
import Data.Hashable(Hashable)
import GHC.Generics (Generic)
import Prelude hiding (lookup)
import Data.Maybe (isJust)

newtype TypeAppRenameMap = TyAppReMap (HM.HashMap Name Name) deriving (Show, Eq, Read, Data, Typeable, Generic)

empty :: TypeAppRenameMap
empty = TyAppReMap HM.empty

insert :: Name -> Name -> TypeAppRenameMap -> TypeAppRenameMap
insert run env (TyAppReMap tarm) = TyAppReMap $ HM.insert run env tarm 

lookup :: Name -> TypeAppRenameMap -> Maybe Name
lookup n (TyAppReMap tarm) = HM.lookup n tarm 

member :: Name -> TypeAppRenameMap -> Bool 
member n tarm = isJust (lookup n tarm)

instance Hashable TypeAppRenameMap