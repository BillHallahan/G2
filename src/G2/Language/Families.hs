{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module G2.Language.Families ( Families
                            , Family (..)
                            , Axiom (..)
                            , mkFamilies ) where

import G2.Language.Syntax

import GHC.Generics (Generic)
import Data.Data (Data, Typeable)
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM

type Families = HM.HashMap Name Family

newtype Family = Family { axioms :: [Axiom] }
              deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Family

-- An equality between a type function application and some type
data Axiom = Axiom { lhs_types :: [Type] -- ^ Type arguments to match on
                   , rhs_type :: Type -- ^ RHS of type equality 
                   }
                   deriving (Show, Eq, Read, Generic, Typeable, Data)

instance Hashable Axiom

mkFamilies :: [(Name, Axiom)] -> Families
mkFamilies = foldl' addAxiom HM.empty
    where
        addAxiom fams (n, ax) =
            HM.alter (Just . maybe (Family [ax]) (ins ax)) n fams
        
        ins ax (Family axs) = Family (ax:axs)