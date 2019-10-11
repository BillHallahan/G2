module G2.Liquid.Inference.FuncConstraint ( FuncConstraint (..)
                                          , FuncConstraints
                                          , emptyFC
                                          , insertFC
                                          , lookupFC ) where

import G2.Language.Syntax

import Data.Coerce
import qualified Data.Map as M

newtype FuncConstraints = FuncConstraints (M.Map Name [FuncConstraint])
                          deriving (Eq, Show, Read)

data FuncConstraint = Pos { constraint :: FuncCall }
                    | Neg { constraint :: FuncCall }
                    deriving (Eq, Show, Read)


emptyFC :: FuncConstraints
emptyFC = FuncConstraints M.empty

insertFC :: FuncConstraint -> FuncConstraints -> FuncConstraints
insertFC fc = coerce (M.insertWith (++) (funcName . constraint $ fc) [fc])

lookupFC :: Name -> FuncConstraints -> [FuncConstraint]
lookupFC n = M.findWithDefault [] n . coerce