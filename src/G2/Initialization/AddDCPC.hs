{-# LANGUAGE OverloadedStrings #-}

module G2.Initialization.AddDCPC (addToDCPC) where

import G2.Config
import G2.Execution.DataConPCMap
import G2.Initialization.Types as IT
import G2.Language.AlgDataTy
import G2.Language.Expr
import qualified G2.Language.KnownValues as KV
import G2.Language.Syntax
import qualified G2.Language.Typing as T
import qualified G2.Language.TyVarEnv as TV

import qualified Data.Foldable as F
import qualified Data.HashMap.Lazy as HM

addToDCPC :: Config -> IT.SimpleState -> DataConPCMap -> DataConPCMap
addToDCPC (Config { smt_prim_lists = UseSMTSeq { add_to_dcs = True } }) (IT.SimpleState { IT.known_values = kv, IT.type_env = tenv }) dcpc =
    let
      tys = filter (to_smt . snd) $ HM.toList tenv
      dcs = concatMap (\(_, adt) -> data_cons adt) tys

      dcpc_prim = addGenericListToDCPCMap kv dcpc
      
      dcpc_map = F.foldl' (addArbDC kv) dcpc_prim dcs
    in
    dcpc_map
addToDCPC _ _ dcpc = dcpc

addGenericListToDCPCMap :: KV.KnownValues -> DataConPCMap -> DataConPCMap
addGenericListToDCPCMap kv dcpc =
    let t = TyVar (Id (Name "__!!__G2_TYVAR" Nothing 0 Nothing) TYPE) in
      addToDCPCMap (KV.dcEmpty kv) [t] (listEmpty t kv TV.empty)
    . addToDCPCMap (KV.dcCons kv) [t] (listCons t kv TV.empty)
    $ dcpc

addArbDC :: KV.KnownValues -> DataConPCMap -> DataCon -> DataConPCMap
addArbDC kv dcpc dc = addToDCPCMap (dc_name dc) (map TyVar $ dc_univ_tyvars dc) (arbDC kv TV.empty dc) dcpc