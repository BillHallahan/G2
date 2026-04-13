{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses, OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}

module G2.Interface.ExecRes ( ExecRes (..), StartFunc, printInputOutput ) where

import G2.Language
import G2.Lib.Printers

import Data.Maybe
import qualified Data.Sequence as S
import qualified Data.Text as T
import qualified Data.HashMap.Lazy as M
import G2.Language.KnownValues (KnownValues(dcEmpty))
import qualified G2.Language.TypeEnv as TE

type StartFunc = T.Text

-- | A fully executed `State`.
data ExecRes t = ExecRes { final_state :: State t -- ^ The final state.
                         , conc_args :: [Expr] -- ^ Fully concrete arguments for the state.
                         , conc_out :: Expr -- ^ Fully concrete output (final `curr_expr`) for the state
                         , conc_sym_gens :: S.Seq Expr 
                         , conc_mutvars :: [(Name, MVOrigin, Expr)]
                         , conc_handles :: [(Name, Expr)]
                         , violated :: Maybe FuncCall -- ^ A violated assertion
                         , validated :: Maybe Bool
                         } deriving (Show, Read)

printInputOutput :: PrettyGuide
                 -> Id -- ^ Input function
                 -> Bindings
                 -> ExecRes t
                 -> (T.Text, T.Text, T.Text, T.Text, T.Text) -- ^ Mutable variables, input, output, handles
printInputOutput pg i (Bindings { input_coercion = c }) er =
    let
        er' = er { conc_args = modifyASTs remMutVarPrim (conc_args er)
                 , conc_out = modifyASTs remMutVarPrim (conc_out er)
                 , conc_sym_gens = modifyASTs remMutVarPrim (conc_sym_gens er)
                 , conc_mutvars = modifyASTs remMutVarPrim (conc_mutvars er) }
        
        -- Set up mappings for generated ADTs in the PrettyGuide so printGenADTs and printInputFunc can use the same mappings.
        pg_gen_adt = updatePGTrackGenADTNames er' pg
    in
    -- TODO: pass updated PG to other printers?
    (printGenADTs pg_gen_adt er', printMutVars pg er', printInputFunc pg_gen_adt c i er', printOutput pg er', printHandles pg er')

updatePGTrackGenADTNames :: ExecRes t -> PrettyGuide -> PrettyGuide
updatePGTrackGenADTNames (ExecRes {conc_args = cas, final_state = State {type_env = tenv}}) pg
    = updatePGADTs pg (M.elems $ filterTEToNeededGenADTs cas tenv)

filterTEToNeededGenADTs :: [Expr] -> TypeEnv -> TypeEnv
filterTEToNeededGenADTs arg_exprs tenv = go M.empty gen_adts_in_args
    where
        gen_adts_in_args = TE.filterTE (anyDCsInNames arg_exprs) all_gen_adts -- only ADTs with constructors in the arguments (acts as "seed set")
        -- Checks recursively if new generated ADTs are present in the names of those in the limited TypeEnv.
        -- Outputs may print generated ADTs that do not seem to appear in the expression. example:
        --      data GenT'2  = GenC'2 :: GenT'2 -> GenT'2 | GenN'2 :: GenT'2
        --      data GenT a = GenC :: (forall a . a -> (GenT a) -> (GenT a)) | GenN :: (forall a . (GenT a))
        --      polyFuncArgTwoKinds (\fs -> case fs GenN of
        --          GenC fs'3 fs'2 -> 1
        --          GenN  -> 0) = 0
        -- This is because (fs'3 :: GenT'2), and types are not printed in outputs. TODO: does this leave out information
        go :: TypeEnv -> TypeEnv -> TypeEnv
        go prev new | prev == new = new
                    | otherwise = go new updated
                    where
                    updated = TE.filterTE (anyDCsInNames new) all_gen_adts
        all_gen_adts = TE.filterToGenADTs tenv -- get only generated ADTs
        
        anyDCsInNames :: (Named a) => a -> AlgDataTy -> Bool
        anyDCsInNames nd adt = any (`elem` names nd) (names $ dataCon adt)

printMutVars :: PrettyGuide -> ExecRes t -> T.Text
printMutVars pg (ExecRes { final_state = s, conc_mutvars = mv@(_:_) }) =
        let 
            bound = T.intercalate "; "
                  . map (\(n, _, e) -> "(# _, " <> printName pg n <> " #) = newMutVar# " <> printHaskellPG pg s e <> " realWorld#")
                  $ filter (\(_, m, _) -> m == MVSymbolic) mv
        in
        "let " <> bound <> " in "
printMutVars _ _ = ""

printInputFunc :: PrettyGuide -> Maybe Coercion -> Id -> ExecRes t -> T.Text
printInputFunc pg m_c i (ExecRes { final_state = s, conc_args = ars }) = printHaskellPG (setTyLamPrinting OmitTyLam pg) s $ mkApp (app_maybe_coer m_c (Var i):ars)
    where
        app_maybe_coer Nothing e = e
        app_maybe_coer (Just c) e = Cast e c

printOutput :: PrettyGuide -> ExecRes t -> T.Text
printOutput _ (ExecRes { final_state = s}) | errorRaised s = "error"
printOutput pg (ExecRes { final_state = s, conc_out = e }) = printHaskellPG pg s e

remMutVarPrim :: Expr -> Expr
remMutVarPrim (Prim (MutVar n) _) = Var $ Id n TyUnknown
remMutVarPrim e = e

printHandles :: PrettyGuide -> ExecRes t -> T.Text
printHandles pg (ExecRes { final_state = s, conc_handles = h })= T.intercalate "\n" . mapMaybe (uncurry (printHandle pg s)) $ h

printHandle :: PrettyGuide -> State t -> Name -> Expr -> Maybe T.Text
printHandle _ s _ e | (Data (DataCon { dc_name = n }):_) <- unApp e
                    , n == dcEmpty (known_values s) = Nothing
printHandle pg s n h = Just (" --- " <> printName pg n <> " --- \n\t" <> printHaskellPG pg s h)

printGenADTs :: PrettyGuide -> ExecRes t -> T.Text
printGenADTs pg (ExecRes {conc_args = cas, final_state = (State {tyvar_env = tvenv, type_env = tenv})}) 
    = let adts_text = prettyTypeEnv tvenv pg (filterTEToNeededGenADTs cas tenv)
    in if adts_text == T.empty then T.empty else adts_text <> "\n"

instance Named t => Named (ExecRes t) where
    names :: Named t => ExecRes t -> S.Seq Name
    names (ExecRes { final_state = s
                   , conc_args = es
                   , conc_out = r
                   , conc_sym_gens = g
                   , conc_mutvars = mv
                   , conc_handles = h
                   , violated = fc }) =
                      names s <> names es <> names r <> names g <> names mv <> names h <> names fc

    rename old new (ExecRes { final_state = s
                            , conc_args = es
                            , conc_out = r
                            , conc_sym_gens = g
                            , conc_mutvars = mv
                            , conc_handles = h
                            , violated = fc
                            , validated = v }) =
      ExecRes { final_state = rename old new s
              , conc_args = rename old new es
              , conc_out = rename old new r
              , conc_sym_gens = rename old new g
              , conc_mutvars = rename old new mv
              , conc_handles = rename old new h
              , violated = rename old new fc
              , validated = v}

    renames hm (ExecRes { final_state = s
                        , conc_args = es
                        , conc_out = r
                        , conc_sym_gens = g
                        , conc_mutvars = mv
                        , conc_handles = h
                        , violated = fc
                        , validated =  v}) =
      ExecRes { final_state = renames hm s
              , conc_args = renames hm es
              , conc_out = renames hm r
              , conc_sym_gens = renames hm g
              , conc_mutvars = renames hm mv
              , conc_handles = renames hm h
              , violated = renames hm fc
              , validated = v }

instance ASTContainer t Expr => ASTContainer (ExecRes t) Expr where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , conc_sym_gens = g
                           , conc_mutvars = mv
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs g ++ containedASTs mv ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , conc_sym_gens = g
                                   , conc_mutvars = mv
                                   , conc_handles = h
                                   , violated = fc
                                   , validated = v }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , conc_sym_gens = modifyContainedASTs f g
                , conc_mutvars = modifyContainedASTs f mv
                , conc_handles = h
                , violated = modifyContainedASTs f fc
                , validated = v}

instance ASTContainer t Type => ASTContainer (ExecRes t) Type where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , conc_sym_gens = g
                           , conc_mutvars = mv
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs g ++ containedASTs mv ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , conc_sym_gens = g
                                   , conc_mutvars = mv
                                   , conc_handles = h
                                   , violated = fc
                                   , validated = v }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , conc_sym_gens = modifyContainedASTs f g
                , conc_mutvars = modifyContainedASTs f mv
                , conc_handles = h
                , violated = modifyContainedASTs f fc
                , validated = v }
