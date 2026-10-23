{-# LANGUAGE DeriveDataTypeable, DeriveGeneric,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses #-}

module G2.Language.FuncConstraints ( FuncConstraints
                                   , FuncConstraint (..)
                                   , FCSplitOn (..)
                                   , FCStatus (..)
                                   , VarLitEqualities
                                   , FCStateType (..)
                                   , nullFC
                                   , lookupFC
                                   , insertFC
                                   , insertListFC
                                   , deleteFC
                                   , mapFC
                                   , mapFCM
                                   , mapAccumFCM
                                   , filterFC
                                   , traverseWithKeyFC
                                   , toListFC
                                   , elemsFC
                                   , emptyFC
                                   , singletonFC
                                   , fromListFC ) where

import G2.Language.AST
import G2.Language.Naming
import G2.Language.Syntax

import Data.Hashable
import qualified Data.HashMap.Lazy as HM

import GHC.Generics (Generic)
import Data.Coerce
import Data.Data (Data)
import Data.Traversable

-- | Constraints on higher order functions
data FuncConstraint =
    FC { fc_preconds :: [Expr]
       , fc_args :: [Expr]
       , fc_ret :: Expr

       , fc_split_on :: [FCSplitOn] -- ^ Used during solver- have we used a predicate to split the ith argument?
       }
       deriving (Eq, Show, Read, Generic, Data)

instance Hashable FuncConstraint

data FCSplitOn = Split | NoSplit
                 deriving (Eq, Show, Read, Generic, Data)

instance Hashable FCSplitOn


data FCStatus = InitialRun -- ^ Not yet to solving function constraints
              | SolvingFCs VarLitEqualities -- ^ In the process of solving function constraints. Generated constraints
                                       -- should be preconditionde on the list of Ids and Lits being equal.
              | SolvedFCs -- ^ Function constraints have been solved
              deriving (Eq, Show, Read, Generic, Data)

instance Hashable FCStatus

type VarLitEqualities = [(Id, Lit)]

data FCStateType = PostCall
                 | FuncArg
                 deriving (Eq, Show, Read, Generic, Data)

instance Hashable FCStateType

newtype FuncConstraints = FCs (HM.HashMap Name [FuncConstraint])
                          deriving (Eq, Show, Read, Generic, Data, Named)

instance Hashable FuncConstraints

nullFC :: FuncConstraints -> Bool
nullFC (FCs fcs) = HM.null fcs

lookupFC :: Name -> FuncConstraints -> Maybe [FuncConstraint]
lookupFC n (FCs fcs) = HM.lookup n fcs

insertFC :: Name -> FuncConstraint -> FuncConstraints -> FuncConstraints
insertFC n fc = coerce (HM.insertWith (++) n [fc])

insertListFC :: Name -> [FuncConstraint] -> FuncConstraints -> FuncConstraints
insertListFC n fc = coerce (HM.insertWith (++) n fc)

deleteFC :: Name -> FuncConstraints -> FuncConstraints
deleteFC n (FCs fcs)= FCs (HM.delete n fcs)

mapFC :: ([FuncConstraint] -> [FuncConstraint]) -> FuncConstraints -> FuncConstraints
mapFC f = coerce (HM.map f)

mapFCM :: Monad m => ([FuncConstraint] -> m [FuncConstraint]) -> FuncConstraints -> m FuncConstraints
mapFCM f (FCs fcs)= FCs <$> mapM f fcs

filterFC :: ([FuncConstraint] -> Bool) -> FuncConstraints -> FuncConstraints
filterFC p (FCs fcs) = FCs (HM.filter p fcs)

mapAccumFCM :: Monad m =>
               (s -> [FuncConstraint] -> m (s, [FuncConstraint]))
            -> s
            -> FuncConstraints
            -> m (s, FuncConstraints)
mapAccumFCM f s (FCs fcs) = fmap FCs <$> mapAccumM f s fcs

traverseWithKeyFC :: Applicative f =>
                     (Name -> [FuncConstraint] -> f [FuncConstraint])
                  -> FuncConstraints
                  -> f FuncConstraints
traverseWithKeyFC f (FCs fcs) = FCs <$> HM.traverseWithKey f fcs

toListFC :: FuncConstraints -> [(Name, [FuncConstraint])]
toListFC = HM.toList . coerce

elemsFC :: FuncConstraints -> [[FuncConstraint]]
elemsFC (FCs fcs) = HM.elems fcs

emptyFC :: FuncConstraints
emptyFC = FCs HM.empty

singletonFC :: Name -> [FuncConstraint] -> FuncConstraints
singletonFC n fc = FCs (HM.singleton n fc)

fromListFC :: [(Name, [FuncConstraint])] -> FuncConstraints
fromListFC = coerce . HM.fromListWith (++)

instance ASTContainer FuncConstraints Expr where
    modifyContainedASTs f (FCs fcs) = FCs (modifyContainedASTs f fcs)
    containedASTs (FCs fcs) = containedASTs fcs

instance ASTContainer FuncConstraints Type where
    modifyContainedASTs f (FCs fcs) = FCs (modifyContainedASTs f fcs)
    containedASTs (FCs fcs) = containedASTs fcs

instance Named FuncConstraint where
    names fc = names (fc_preconds fc) <> names (fc_args fc) <> names (fc_ret fc)
    rename old new fc = fc { fc_preconds = rename old new (fc_preconds fc)
                           , fc_args = rename old new (fc_args fc)
                           , fc_ret = rename old new (fc_ret fc) }
    renames hm fc = fc { fc_preconds = renames hm (fc_preconds fc)
                       , fc_args = renames hm (fc_args fc)
                       , fc_ret = renames hm (fc_ret fc) }

instance ASTContainer FuncConstraint Expr where
    modifyContainedASTs f fc = fc { fc_preconds = map f (fc_preconds fc)
                                  , fc_args = map f (fc_args fc)
                                  , fc_ret = f (fc_ret fc) }
    containedASTs fc = containedASTs (fc_preconds fc) <> containedASTs (fc_args fc) <> containedASTs (fc_ret fc)

instance ASTContainer FuncConstraint Type where
    modifyContainedASTs f fc = fc { fc_preconds = modifyContainedASTs f (fc_preconds fc)
                                  , fc_args = modifyContainedASTs f (fc_args fc)
                                  , fc_ret = modifyContainedASTs f (fc_ret fc) }
    containedASTs fc = containedASTs (fc_preconds fc) <> containedASTs (fc_args fc) <> containedASTs (fc_ret fc)
