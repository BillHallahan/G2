module G2.Translation.TransTypes where

import CoreSyn
import GHC
import HscTypes

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T

import qualified G2.Language as G2

type NameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name

type TypeNameMap = HM.HashMap (T.Text, Maybe T.Text) G2.Name

type ExportedName = G2.Name


-- Data necessary from Ghc to compile Haskell module(s) into G2 Core
data CompileClosure = CompileClosure
  { mod_name :: Maybe String
  , tycon_data :: [[TyCon]]
  , bindings :: [([CoreBind], Maybe ModBreaks)]
  , cls_inst :: [ClsInst]
  , mod_det_types :: [TypeEnv]
  , exported_names :: [ExportedName]
  }


data ModDetailsCompileClosure = ModDetailsCompileClosure
  { mod_det_cls_insts :: [ClsInst]
  , mod_det_tyenv :: TypeEnv
  , mod_det_exports :: [ExportedName]
  }

data CgGutsCompileClosure = CgGutsCompileClosure
  { cg_mod_name :: Maybe String
  , cg_bindings :: [CoreBind]
  , cg_breaks :: Maybe ModBreaks
  , cg_tycons :: [TyCon]
  } 



