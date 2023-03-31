{-# LANGUAGE CPP #-}

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)

module G2.Translation.GHC ( module GHC
                          , module GHC.Core
                          , module GHC.Core.Class
                          , module GHC.Core.Coercion
                          , module GHC.Core.DataCon
                          , module GHC.Core.InstEnv
                          , module GHC.Core.TyCo.Rep
                          , module GHC.Core.TyCon
                          , module GHC.Data.FastString
                          , module GHC.Data.Pair
                          , module GHC.Driver.Main
                          , module GHC.Driver.Session
                          , module GHC.Iface.Tidy
                          , module GHC.Paths
                          , module GHC.Types.Avail
                          , module GHC.Types.Id.Info
                          , module GHC.Types.Literal
                          , module GHC.Types.Name
                          , module GHC.Types.SrcLoc
                          , module GHC.Types.Unique
                          , module GHC.Types.Var
                          , module GHC.Unit.Types
#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
                          , module GHC.Platform.Ways
                          , module GHC.Types.Tickish
                          , module GHC.Types.TypeEnv
                          , module GHC.Unit.Module.Deps
                          , module GHC.Unit.Module.ModDetails
                          , module GHC.Unit.Module.ModGuts

                          , HscTarget
#else
                          , module GHC.Driver.Types
                          , module GHC.Driver.Ways
#endif
#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
                          , module GHC.Driver.Config.Tidy
#endif
                          ) where

import GHC
import GHC.Core ( Alt (..)
                , AltCon (..)
                , Bind (..)
                , CoreAlt
                , CoreBind
                , CoreExpr
                , CoreProgram
                , CoreRule (..)
                , Expr (..)

#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
#else
                , Tickish (..)
#endif

                , bindersOf)
import GHC.Core.Class (classAllSelIds, className, classSCTheta, classTyVars)
import GHC.Core.Coercion
import GHC.Core.DataCon
import GHC.Core.InstEnv
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon
import GHC.Data.FastString
import GHC.Data.Pair
import GHC.Driver.Main
import GHC.Driver.Session
import GHC.Iface.Tidy
import GHC.Paths
import GHC.Types.Avail
import GHC.Types.Id.Info
import GHC.Types.Literal
import GHC.Types.Name hiding (varName)
import GHC.Types.SrcLoc
import GHC.Types.Unique
import GHC.Types.Var
import GHC.Unit.Types

#if MIN_VERSION_GLASGOW_HASKELL(9,3,0,0)
import GHC.Driver.Config.Tidy
#endif

#if MIN_VERSION_GLASGOW_HASKELL(9,2,0,0)
import GHC.Platform.Ways
import GHC.Types.Tickish
import GHC.Types.TypeEnv
import GHC.Unit.Module.Deps
import GHC.Unit.Module.ModDetails
import GHC.Unit.Module.ModGuts

type HscTarget = Backend
#else
import GHC.Driver.Types
import GHC.Driver.Ways
#endif


#else

module G2.Translation.GHC ( module Avail
                          , module Class
                          , module Coercion
                          , module CoreSyn
                          , module DataCon
                          , module DynFlags
                          , module FastString
                          , module GHC
                          , module GHC.Paths
                          , module HscMain
                          , module HscTypes
                          , module IdInfo
                          , module InstEnv
                          , module Literal
                          , module Name
                          , module Pair
                          , module SrcLoc
                          , module TidyPgm
                          , module TyCon
                          , module TyCoRep
                          , module Unique
                          , module Var) where

import Avail
import Class (classAllSelIds, className, classSCTheta, classTyVars)
import Coercion
import CoreSyn
import DataCon
import DynFlags
import FastString
import GHC hiding (AnnKeywordId (..), AnnExpr' (..))
import GHC.Paths
import HscMain
import HscTypes
import IdInfo
import InstEnv
import Literal
import Name hiding (varName)
import Pair
import SrcLoc
import TidyPgm
import TyCon
import TyCoRep
import Unique
import Var

#endif
