--  | Some functions (mostly numeric functions) have specifications that exactly capture there behavior,
-- and thus do not need to be checked.  This module removes these specifications, as evaluating them wastes time.

{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.RemoveRedundantAsserts (removeRedundantAsserts) where

import G2.Language
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashSet as HS
import qualified Data.Text as T

removeRedundantAsserts :: LHStateM ()
removeRedundantAsserts = mapWithKeyME removeRedundantAsserts'

removeRedundantAsserts' :: Name -> Expr -> LHStateM Expr
removeRedundantAsserts' (Name n m _ _) e
    | (n, m) `HS.member` removeFrom = return $ elimAsserts e
    | otherwise = return e

removeFrom :: HS.HashSet (T.Text, Maybe T.Text)
removeFrom = HS.fromList [ ("+", Just "GHC.Num")
                         , ("-", Just "GHC.Num")
                         , ("*", Just "GHC.Num")
                         , ("negate", Just "GHC.Num")
                         , ("abs", Just "GHC.Num")
                         , ("signum", Just "GHC.Num")
                         , ("fromInteger", Just "GHC.Num")

                         , ("quot", Just "GHC.Real")
                         , ("rem", Just "GHC.Real")
                         , ("div", Just "GHC.Real")
                         , ("mod", Just "GHC.Real")
                         , ("quotRem", Just "GHC.Real")
                         , ("divMod", Just "GHC.Real")
                         , ("toInteger", Just "GHC.Real")

                         , ("==", Just "GHC.Classes")
                         , ("/=", Just "GHC.Classes")

                         , ("<", Just "GHC.Classes")
                         , ("<=", Just "GHC.Classes")
                         , (">", Just "GHC.Classes")
                         , (">=", Just "GHC.Classes")

                         , ("I#", Just "GHC.Types")
                         , ("True", Just "GHC.Types")
                         , ("False", Just "GHC.Types")]