{-# LANGUAGE OverloadedStrings #-}

-- | Adjust functions to allow calling SMT variants.
module G2.SMTSynth.Integrate (integrateSMTDef) where

import qualified G2.Initialization.Types as IT
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import qualified G2.Language.TyVarEnv as TV

import Data.Foldable
import qualified Data.HashMap.Strict as HM
import Data.List
import Data.Maybe
import Data.Monoid hiding (Alt)
import qualified Data.Text as T

integrateSMTDef :: IT.SimpleState -> IT.SimpleState
integrateSMTDef s@(IT.SimpleState { IT.expr_env = orig_eenv, IT.known_values = kv, IT.name_map = nm }) =
    let
        smt_defs = HM.elems $ HM.filterWithKey (\(_, m) _ -> fmap (T.take 4) m == Just "SMT.") nm
    in
    s { IT.expr_env = foldl' go orig_eenv smt_defs }
    where
        go eenv smt_n@(Name occ_name md _ _) =
            let
                -- Get occurrence name/module of the original function. Requires dropping "smt_" from the start of the function
                -- name, and "SMT." from the start of the module name.
                (ti, a_md) = adjMod md
                orig_nm = (T.drop 4 occ_name, a_md)
            in
            case HM.lookup orig_nm nm of
                Just n | Just e <- E.lookup n eenv -> E.insert n (adjust smt_n ti e) eenv
                _ -> eenv
        
        adjust smt_n ti e =
            let is = leadingLamIds e in
            insertInLams (\_ -> adjust' is smt_n ti) e

        adjust' is smt_n ti e
            | containsTypeIndex e = addTypeIndexAlt is smt_n ti e
            | otherwise = addTypeIndexCase is smt_n ti e

        addTypeIndexCase is smt_n ti e =
            let
                list_is = filter (\(Id _ t) -> is_rel_list t) is
            in
            case list_is of
                [] -> e
                (i:_) ->
                    let
                        ty_ind_call = mkApp [Var type_index, Type (typeOf TV.empty i), Var i]
                        bindee = foldl' add_adj_str ty_ind_call list_is
                    in
                    Case bindee
                        (Id placeholder TyUnknown)
                        (typeOf TV.empty e)
                        [ Alt (LitAlt (LitInt ti)) . mkApp $ Var (Id smt_n TyUnknown):map Var is
                        , Alt Default e]
        
        addTypeIndexAlt is smt_n ti = modify at_go
            where
                at_go (Case bindee i t as) | containsTypeIndex bindee =
                    let new_alt = Alt (LitAlt (LitInt ti)) . mkApp $ Var (Id smt_n TyUnknown):map Var is in
                    Case bindee i t (new_alt:as)
                at_go e = e
        
        containsTypeIndex = getAny . eval containsTypeIndex'
        containsTypeIndex' (Var (Id n _)) = Any $ n == KV.typeIndex kv
        containsTypeIndex' _ = Any False

        is_rel_list (TyApp (TyCon n _) (TyVar _)) = n == KV.tyList kv
        is_rel_list _ = False

        add_adj_str c i = mkApp [Var adj_str, Type (get_tyvar i), c, Var i]

        get_tyvar (Id _ (TyApp _ t@(TyVar _))) = t
        get_tyvar _ = error "get_tyvar: impossible - not a list"

        placeholder = Name "!!__G2__!!__placeholder" Nothing 0 Nothing

        adj_str = toId (KV.adjStr kv)
        type_index = toId (KV.typeIndex kv)

        toId n = Id n . fromMaybe TyUnknown . fmap (typeOf TV.empty) $ E.lookup n orig_eenv

adjMod :: Maybe T.Text -> (Integer, Maybe T.Text)
adjMod (Just md)
    | md'@(Just _) <- T.stripPrefix "SMT.String" md = (1, md')
    | md'@(Just _) <- T.stripPrefix "SMT.SeqInt" md = (2, md')
    | otherwise = error "adjMod: Module not recognized"
adjMod Nothing = error "adjMod: Module not recognized"