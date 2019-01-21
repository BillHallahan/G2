{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module G2.Interface.OutputTypes ( ExecRes (..)) where

import G2.Language

-- | A fully executed State
data ExecRes t = ExecRes { final_state :: State t
                         , conc_args :: [Expr]
                         , conc_out :: Expr
                         , violated :: Maybe FuncCall -- ^ A violated assertion
                         , exec_bindings :: Bindings
                         } deriving (Show, Read)

instance Named t => Named (ExecRes t) where
    names (ExecRes { final_state = s
                   , conc_args = es
                   , conc_out = r
                   , violated = fc 
                   , exec_bindings = b}) =
                      names s ++ names es ++ names r ++ names fc ++ names b

    rename old new (ExecRes { final_state = s
                            , conc_args = es
                            , conc_out = r
                            , violated = fc 
                            , exec_bindings = b}) =
      ExecRes { final_state = rename old new s
              , conc_args = rename old new es
              , conc_out = rename old new r
              , violated = rename old new fc 
              , exec_bindings = rename old new b}

    renames hm (ExecRes { final_state = s
                        , conc_args = es
                        , conc_out = r
                        , violated = fc 
                        , exec_bindings = b}) =
      ExecRes { final_state = renames hm s
              , conc_args = renames hm es
              , conc_out = renames hm r
              , violated = renames hm fc 
              , exec_bindings = renames hm b}

instance ASTContainer t Expr => ASTContainer (ExecRes t) Expr where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , violated = fc 
                           , exec_bindings = b}) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs fc ++ containedASTs b

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , violated = fc 
                                   , exec_bindings = b}) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , violated = modifyContainedASTs f fc 
                , exec_bindings = modifyContainedASTs f b}

instance ASTContainer t Type => ASTContainer (ExecRes t) Type where
    containedASTs (ExecRes { final_state = s
                           , conc_args = es
                           , conc_out = r
                           , violated = fc 
                           , exec_bindings = b}) =
      containedASTs s ++ containedASTs es ++ containedASTs r ++ containedASTs fc ++ containedASTs b

    modifyContainedASTs f (ExecRes { final_state = s
                                   , conc_args = es
                                   , conc_out = r
                                   , violated = fc 
                                   , exec_bindings = b}) =
        ExecRes { final_state = modifyContainedASTs f s
                , conc_args = modifyContainedASTs f es
                , conc_out = modifyContainedASTs f r
                , violated = modifyContainedASTs f fc 
                , exec_bindings = modifyContainedASTs f b}
