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

import qualified Data.HashMap.Lazy as HM

addToDCPC :: Config -> IT.SimpleState -> DataConPCMap -> DataConPCMap
addToDCPC (Config { smt_prim_lists = UseSMTSeq { add_to_dcs = True } }) (IT.SimpleState { IT.known_values = kv, IT.type_env = tenv }) dcpc =
    let
      tys = filter (to_smt . snd) $ HM.toList tenv
      ty_cons = map (\(n, adt) ->
                        let
                          bi = bound_ids adt
                          kind = T.mkTyFun (map (\(Id _ t) -> t) bi ++ [TYPE])
                        in
                        T.mkTyApp $ TyCon n kind:map TyVar bi
                    ) tys

      dcpc_prim = addWrappedListToDCPCMap kv (mkDCDouble kv tenv) TyLitDouble
                . addWrappedListToDCPCMap kv (mkDCFloat kv tenv) TyLitFloat
                . addWrappedListToDCPCMap kv (mkDCInteger kv tenv) TyLitInt
                . addWrappedListToDCPCMap kv (mkDCInt kv tenv) TyLitInt $ dcpc
    in
    foldl' (addListToDCPCMap kv) dcpc_prim ty_cons
addToDCPC _ _ dcpc = dcpc

addWrappedListToDCPCMap :: KV.KnownValues -> Expr -> Type -> DataConPCMap -> DataConPCMap
addWrappedListToDCPCMap kv dc t =
      addToDCPCMap (KV.dcEmpty kv) [T.returnType $ T.typeOf TV.empty dc] (listEmpty t kv TV.empty)
    . addToDCPCMap (KV.dcCons kv) [T.returnType $ T.typeOf TV.empty dc] (wrapperListCons dc t kv TV.empty)

addListToDCPCMap :: KV.KnownValues -> DataConPCMap -> Type -> DataConPCMap
addListToDCPCMap kv dcpc t =
      addToDCPCMap (KV.dcEmpty kv) [t] (listEmpty t kv TV.empty)
    . addToDCPCMap (KV.dcCons kv) [t] (listCons t kv TV.empty)
    $ dcpc
