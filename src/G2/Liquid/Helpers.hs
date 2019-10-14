{-# LANGUAGE CPP #-}

module G2.Liquid.Helpers ( getGHCInfos
						 , funcSpecs
						 , findFuncSpec
						 , measureSpecs
						 , varEqName
						 , namesEq ) where

import G2.Language.Syntax as G2

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types hiding (Config, cls, names)
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Haskell.Liquid.UX.CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LHC

import qualified Language.Fixpoint.Types.PrettyPrint as FPP

import Data.List
import qualified Data.Text as T

import GHC as GHC
import Name
import Var as V

getGHCInfos :: LHC.Config -> [FilePath] -> [FilePath] -> [FilePath] -> IO [GhcInfo]
getGHCInfos config proj fp lhlibs = do
    let config' = config {idirs = idirs config ++ proj ++ lhlibs
                         , files = files config ++ lhlibs
                         , ghcOptions = ["-v"]}

    -- GhcInfo
    (ghci, _) <- LHI.getGhcInfos Nothing config' fp

    return ghci
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
#if MIN_VERSION_liquidhaskell(0,8,6)
funcSpecs fs = concatMap (gsTySigs . gsSig . giSpec) fs -- Functions asserted in LH
            ++ concatMap (gsAsmSigs . gsSig . giSpec) fs -- Functions assumed in LH
#else
funcSpecs fs = concatMap (gsTySigs . spec) fs -- Functions asserted in LH
            ++ concatMap (gsAsmSigs . spec) fs -- Functions assumed in LH
#endif

findFuncSpec :: [GhcInfo] -> G2.Name -> Maybe SpecType
findFuncSpec ghci g2_n =
	let
		fs = funcSpecs ghci
		fs' = map (\(v, lst) -> (V.varName v, lst)) fs
	in
	case find (\(n, _) -> namesEq n g2_n) fs' of
		Just st -> Just . val . snd $ st
		Nothing -> Nothing

varEqName :: V.Var -> G2.Name -> Bool
varEqName v = namesEq (V.varName v)

namesEq :: GHC.Name -> G2.Name -> Bool
namesEq ghc_n (Name n m _ _) =
	T.pack (occNameString $ nameOccName ghc_n) == n
		&& (case nameModule_maybe ghc_n of
				Just mod ->
					Just (T.pack . moduleNameString . moduleName $ mod) == m
				Nothing -> m == Nothing)

measureSpecs :: [GhcInfo] -> [Measure SpecType GHC.DataCon]
#if MIN_VERSION_liquidhaskell(0,8,6)
measureSpecs = concatMap (gsMeasures . gsData . giSpec)
#else
measureSpecs = concatMap (gsMeasures . spec)
#endif
