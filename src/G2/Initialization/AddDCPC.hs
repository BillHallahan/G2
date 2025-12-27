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
      addListToDCPCMap kv (mkDCDouble kv tenv) TyLitDouble
    . addListToDCPCMap kv (mkDCFloat kv tenv) TyLitFloat 
    . addListToDCPCMap kv (mkDCInteger kv tenv) TyLitInt
    . addListToDCPCMap kv (mkDCInt kv tenv) TyLitInt $ dcpc
addToDCPC _ _ dcpc = dcpc

addListToDCPCMap :: KV.KnownValues -> Expr -> Type -> DataConPCMap -> DataConPCMap
addListToDCPCMap kv dc t =
      addToDCPCMap (KV.dcEmpty kv) [T.returnType $ T.typeOf TV.empty dc] (listEmpty t kv TV.empty)
    . addToDCPCMap (KV.dcCons kv) [T.returnType $ T.typeOf TV.empty dc] (listCons dc t kv TV.empty)