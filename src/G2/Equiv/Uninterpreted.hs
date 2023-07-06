{-# LANGUAGE  FlexibleContexts #-}


module G2.Equiv.Uninterpreted where 
 
import G2.Language
import qualified G2.Language.ExprEnv as E
import Data.Foldable
import Data.Maybe 
import qualified Data.HashMap.Lazy as HM  
import qualified G2.Language.TypeEnv as T

-- | Find variables that don't have binding and adjust the epxression environment to treat them as symbolic 
addFreeVarsAsSymbolic :: ExprEnv -> ExprEnv 
addFreeVarsAsSymbolic eenv = let xs = freeVars eenv eenv 
                             in foldl' (flip E.insertSymbolic) eenv xs 

allDC :: ASTContainer t Expr => t -> [DataCon]
allDC = evalASTs allDC' 

-- problem: not generate one list but two separate list
allDC' :: Expr -> [DataCon]
allDC' e = case e of 
    Data dc -> [dc] 
    Case _ _ _ as -> mapMaybe (\(Alt altMatch _) -> case altMatch of 
                                                        DataAlt dc _ -> Just dc
                                                        _ -> Nothing) as 
    _ -> []


-- difference from Data.HashMap.Lazy
-- get all algDataType with elems and  get the DataCon out of a AlgDataTy
--- in e 
freeDC :: ASTContainer e Expr => TypeEnv -> e -> [DataCon]
freeDC typeEnv e = HM.difference . (allDC e) . mapMaybe . (\algDataTy -> data_con algDataTy) (HM.elems typeEnv)

allTypes :: ASTContainer t Type => t -> [(Name, Kind)]
allTypes t = evalASTs (allTypes' t) 

allTypes' :: Type -> [(Name, Kind)]
allTypes' t = case t of 
        (TyCon typename typekind) -> mapMaybe . (\(TyCon typename typekind) -> [(typename,typekind)]) t
        _ -> []

-- argTypesTEnv :: TypeEnv -> [Type]
-- maybe use argTypesTEnv first to get [Type]
-- then uses allTypes to filter the name, kind pair
-- maybe need tweak for alltypes since allTypes handle only 1 at a time
freeTypes :: ASTContainer t Type => TypeEnv -> t -> [(Name, Kind)]
freeTypes typeEnv t = L.difference . (allTypes t) . (allTypes . T.argTypesTEnv $ typeEnv)
