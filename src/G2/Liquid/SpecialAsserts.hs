module G2.Liquid.SpecialAsserts ( addSpecialAsserts
                                , addTrueAsserts
                                , addErrorAssumes) where

import G2.Config
import G2.Language
import qualified G2.Language.ExprEnv as E
import qualified G2.Language.KnownValues as KV
import G2.Language.Monad
import G2.Liquid.Types

import qualified Data.HashSet as S
import qualified Data.Text as T

import Debug.Trace

-- | Adds an assert of false to the function called when a pattern match fails
addSpecialAsserts :: LHStateM ()
addSpecialAsserts = do
    pen <- KV.patErrorFunc <$> knownValues
    pe <- lookupE pen

    let e = case pe  of
            Just e2 -> e2
            Nothing -> Prim Undefined TyBottom

    let fc = FuncCall {funcName = pen, arguments = [], returns = Prim Undefined TyBottom}
    
    false <- mkFalseE
    let e' = Assert (Just fc) false e
    
    insertE pen e'

-- | Adds an Assert of True to any function without an assertion already,
-- excluding certain functions (namely dicts) that we never want to abstract
-- Furthermore, expands all Lambdas as much as possible, so that we get all the arguments
-- for the assertion. 
addTrueAsserts :: Id -> LHStateM ()
addTrueAsserts i = do
    ns <- return . maybe [] varNames =<< lookupE (idName i)
    tc <- return . tcDicts =<< typeClasses
    
    let tc' = map idName tc
        ns' = filter (`notElem` tc') ns
    
    mapWithKeyME (addTrueAsserts' ns')

addTrueAsserts' :: [Name] -> Name -> Expr -> LHStateM Expr
addTrueAsserts' ns n e
    | n `elem` ns =
        insertInLamsE (\is e' ->
                    case e' of
                        Let [(_, _)] (Assert _ _ _) -> return e'
                        _ -> do
                            true <- mkTrueE
                            r <- freshIdN (typeOf e')

                            let fc = FuncCall { funcName = n
                                              , arguments = map Var is
                                              , returns = (Var r)}
                                e'' = Let [(r, e')] $ Assert (Just fc) true (Var r)

                            return e''
                    ) =<< etaExpandToE (numArgs e) e
    | otherwise = return e

-- | Blocks calling error in the functions specified in the block_errors_in in
-- the Config, by wrapping the errors in Assume False
addErrorAssumes :: Config -> LHStateM ()
addErrorAssumes config = mapWithKeyME (addErrorAssumes' (block_errors_in config))

addErrorAssumes' :: S.HashSet (T.Text, Maybe T.Text) -> Name -> Expr -> LHStateM Expr
addErrorAssumes' ns (Name n m _ _) e = do
    kv <- knownValues
    if (n, m) `S.member` ns then addErrorAssumes'' kv e else return e

addErrorAssumes'' :: KnownValues -> Expr -> LHStateM Expr
addErrorAssumes'' kv v@(Var (Id n _))
    | KV.errorFunc kv == n = do
        tre <- trace ("HERE n = " ++ show n) mkTrueE
        return $ Assume Nothing tre v
addErrorAssumes'' kv e = modifyChildrenM (addErrorAssumes'' kv) e
