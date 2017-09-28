module G2.Internals.Initialization.Functionalizer (functionalize) where

import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E

functionalize :: TypeEnv -> ExprEnv -> NameGen -> (TypeEnv, ExprEnv, NameGen)
functionalize tenv eenv ng =
    let
        types = argTypesTEnv tenv ++ funcArgTypes eenv
    in
    (tenv, eenv, ng)


funcsOfType :: Type -> ExprEnv -> [Name]
funcsOfType t = E.keys . E.filter (\e -> t == typeOf e)

-- Returns a list of all argument function types in the type env
argTypesTEnv :: ASTContainer m Type => m -> [Type]
argTypesTEnv = evalASTs argTypesTEnv'

argTypesTEnv' :: Type -> [Type]
argTypesTEnv' t@(TyFun _ _) = [t]
argTypesTEnv' _ = []

-- Returns a list of all argument function types 
funcArgTypes :: ASTContainer m Type => m -> [Type]
funcArgTypes = evalASTs funcArgTypes'

funcArgTypes' :: Type -> [Type]
funcArgTypes' (TyFun t@(TyFun _ _) _) = [t]
funcArgTypes' _ = []