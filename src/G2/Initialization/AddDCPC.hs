module G2.Initialization.AddDCPC (addToDCPC) where

import G2.Config
import G2.Execution.DataConPCMap
import G2.Initialization.Types as IT
import G2.Language.Expr
import qualified G2.Language.KnownValues as KV
-- import G2.Language.Support
import G2.Language.Syntax
import qualified G2.Language.Typing as T
import qualified G2.Language.TyVarEnv as TV

addToDCPC :: Config -> IT.SimpleState -> DataConPCMap -> DataConPCMap
addToDCPC (Config { smt_prim_lists = UseSMTSeq }) (IT.SimpleState { IT.known_values = kv, IT.type_env = tenv }) dcpc =
      addListToDCPCMap kv (mkDCDouble kv tenv) (T.tyDouble kv) 
    . addListToDCPCMap kv (mkDCFloat kv tenv) (T.tyFloat kv) 
    . addListToDCPCMap kv (mkDCInteger kv tenv) (T.tyInteger kv)
    . addListToDCPCMap kv (mkDCInt kv tenv) (T.tyInt kv) $ dcpc
addToDCPC _ _ dcpc = dcpc

addListToDCPCMap :: KV.KnownValues -> Expr -> Type -> DataConPCMap -> DataConPCMap
addListToDCPCMap kv dc t =
      addToDCPCMap (KV.dcEmpty kv) [t] (listEmpty t kv TV.empty)
    . addToDCPCMap (KV.dcCons kv) [t] (listCons dc t kv TV.empty)