{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Interface.OutputTypes ( ExecRes (..)) where

import G2.Language

import qualified Data.Sequence as S

-- | A fully executed `State`.
data ExecRes t = ExecRes { final_state :: State t -- ^ The final state.
                         , conc_args :: [Expr] -- ^ Fully concrete arguments for the state.
                         , conc_out :: Expr -- ^ Fully concrete output (final `curr_expr`) for the state
                         , conc_sym_gens :: S.Seq Expr 
                         , violated :: Maybe FuncCall -- ^ A violated assertion
                         } deriving (Show, Read)

instance Named t => Named (ExecRes t) where
    names (ExecRes { final_state = s
                   , conc_args = es
                   , conc_out = r
                   , conc_sym_gens = g
                   , violated = fc }) =
                      names s <> names es <> names r <> names g <> names fc

    rename old new (ExecRes { final_state = s
                            , conc_args = es
                            , conc_out = r
                            , conc_sym_gens = g
                            , violated = fc }) =
      ExecRes { final_state = rename old new s
              , conc_args = rename old new es
              , conc_out = rename old new r
              , conc_sym_gens = rename old new g
              , violated = rename old new fc}

    renames hm (ExecRes { final_state = s
                        , conc_args = es
                        , conc_out = r
                        , conc_sym_gens = g
                        , violated = fc }) =
      ExecRes { final_state = renames hm s
              , conc_args = renames hm es
              , conc_out = renames hm r
              , conc_sym_gens = renames hm g
              , violated = renames hm fc }

instance ASTContainer t Expr => ASTContainer (ExecRes t) Expr where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , conc_sym_gens = g
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs g ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , conc_sym_gens = g
                                   , violated = fc }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , conc_sym_gens = modifyContainedASTs f g
                , violated = modifyContainedASTs f fc}

instance ASTContainer t Type => ASTContainer (ExecRes t) Type where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , conc_sym_gens = g
                           , violated = fc }) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs g ++ containedASTs fc

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , conc_sym_gens = g
                                   , violated = fc }) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , conc_sym_gens = modifyContainedASTs f g
                , violated = modifyContainedASTs f fc }
