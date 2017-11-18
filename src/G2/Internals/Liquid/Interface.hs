{-# LANGUAGE FlexibleContexts #-}

module G2.Internals.Liquid.Interface where

import G2.Internals.Translation
import G2.Internals.Interface
import G2.Internals.Language
import qualified G2.Internals.Language.ExprEnv as E
import G2.Internals.Execution

import qualified Language.Haskell.Liquid.GHC.Interface as LHI
import Language.Haskell.Liquid.Types
import qualified Language.Haskell.Liquid.Types.PrettyPrint as PPR
import Language.Fixpoint.Types.PrettyPrint
import Language.Haskell.Liquid.UX.CmdLine 

import Var

-- | findCounterExamples
-- Given (several) LH sources, and a string specifying a function name,
-- attempt to find counterexamples to the functions liquid type
findCounterExamples :: [FilePath] -> String -> IO [(State, [Rule], [Expr], Expr)]
findCounterExamples fp entry = do
    ghcInfos <- getGHCInfos fp
    let specs = funcSpecs ghcInfos

    (binds, tycons) <- translation undefined undefined undefined -- proj src prims
    let init_state = initState binds tycons Nothing Nothing Nothing True entry

    let merged_state = mergeLHSpecState specs init_state

    return []

getGHCInfos :: [FilePath] -> IO [GhcInfo]
getGHCInfos fp = do
    config <- getOpts []
    return . fst =<< LHI.getGhcInfos Nothing config fp
    
funcSpecs :: [GhcInfo] -> [(Var, LocSpecType)]
funcSpecs = concatMap (gsTySigs . spec)

pprint :: (Var, LocSpecType) -> IO ()
pprint (v, r) = do
    let i = mkId v

    let doc = PPR.rtypeDoc Full $ val r
    putStrLn $ show i
    putStrLn $ show doc

-- | mergeLHSpecState
-- Merges a list of Vars and SpecTypes with a State, by finding
-- cooresponding vars between the list and the state, and calling
-- mergeLHSpecState on the corresponding exprs and specs
mergeLHSpecState :: [(Var, LocSpecType)] -> State -> State
mergeLHSpecState [] s = s
mergeLHSpecState ((v,lst):xs) s =
    let
        (Id (Name n m _) _) = mkId v

        g2N = E.lookupNameMod n m (expr_env s)
    in
    case g2N of
        Just (n', e) -> mergeLHSpecState xs $ addSpecType n' e (val lst) s
        Nothing -> error "Can't match LH names to G2 names"

addSpecType :: Name -> Expr -> SpecType -> State -> State
addSpecType n e st s =
    let
        e' = convertSpecType st e
    in
    s {expr_env = E.insert n e' (expr_env s)}

convertSpecType :: SpecType -> Expr -> Expr
convertSpecType = undefined