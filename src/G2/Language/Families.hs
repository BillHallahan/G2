{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, FlexibleContexts, MultiParamTypeClasses #-}

module G2.Language.Families ( Families
                            , Family (..)
                            , Axiom (..)
                            , mkFamilies
                            , fullyReduceTypeFunctions
                            , reduceTypeFunction ) where

import G2.Language.AST
import G2.Language.Syntax
import G2.Language.Typing
import qualified G2.Language.TyVarEnv as TV

import GHC.Generics (Generic)
import Control.Monad
import Data.Data (Data, Typeable)
import Data.Foldable
import Data.Hashable
import qualified Data.HashMap.Lazy as HM
import Data.Maybe

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

fullyReduceTypeFunctions :: Families -> TV.TyVarEnv -> Type -> Type
fullyReduceTypeFunctions fams tv_env = go
    where
        go t | Just t' <- reduceTypeFunction fams tv_env t = go t'
             | otherwise = t

-- | Applies a single rewrite reducing a type function.
-- If the passed `Type` is not a type function application, or if the type function application
-- is not valid (based on the passed `Families`) returns Nothing.
reduceTypeFunction :: Families -> TV.TyVarEnv -> Type -> Maybe Type
reduceTypeFunction fams tv_env t
    | TyCon n _:ts <- unTyApp t
    , Just (Family { axioms = axs }) <- HM.lookup n fams
    , Just ax <- find (isJust . axiomMatches tv_env ts) axs = Just (rhs_type ax)
    | otherwise = Nothing

axiomMatches :: TV.TyVarEnv -> [Type] -> Axiom -> Maybe TV.TyVarEnv
axiomMatches tv_env arg_ts (Axiom { lhs_types = lhs_ts }) =
    foldM (\tv -> uncurry (unify' tv)) tv_env $ zip arg_ts lhs_ts

instance ASTContainer Family Expr where
    containedASTs (Family ax) = containedASTs ax
    modifyContainedASTs f (Family { axioms = ax }) = Family { axioms = modifyContainedASTs f ax }

instance ASTContainer Family Type where
    containedASTs (Family ax) = containedASTs ax
    modifyContainedASTs f (Family { axioms = ax }) = Family { axioms = modifyContainedASTs f ax }

instance ASTContainer Axiom Expr where
    containedASTs (Axiom lhs rhs) = containedASTs lhs <> containedASTs rhs
    modifyContainedASTs f (Axiom { lhs_types = lhs, rhs_type = rhs }) =
        Axiom { lhs_types = modifyContainedASTs f lhs, rhs_type = modifyContainedASTs f rhs }

instance ASTContainer Axiom Type where
    containedASTs (Axiom lhs rhs) = containedASTs lhs <> containedASTs rhs
    modifyContainedASTs f (Axiom { lhs_types = lhs, rhs_type = rhs }) =
        Axiom { lhs_types = modifyContainedASTs f lhs, rhs_type = modifyContainedASTs f rhs }
