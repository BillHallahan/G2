{-# LANGUAGE FlexibleContexts #-}

module G2.Postprocessing.Undefunctionalize (undefunctionalize) where

import G2.Language
import qualified G2.Language.ExprEnv as E

--Switches every occurence of a Var in the Func SLT from datatype to function
undefunctionalize :: ASTContainer m Expr => State t -> Bindings -> m -> m
undefunctionalize s b e = modifyASTs (replaceFuncSLT s b) e

replaceFuncSLT :: State t -> Bindings -> Expr -> Expr
replaceFuncSLT s b v@(Data (DataCon n _)) =
    let
        n' = lookupFuncInterps n (func_table b)
    in
    case n' of
            Just (n'', _) -> Var $ Id n'' (case functionType s n'' of
                                                  Just t -> t
                                                  Nothing -> TyBottom)
            Nothing -> v
replaceFuncSLT _ _ e = e

functionType :: State t -> Name -> Maybe Type
functionType s n = typeOf <$> E.lookup n (expr_env s)
