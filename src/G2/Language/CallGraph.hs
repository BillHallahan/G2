module G2.Language.CallGraph ( CallGraph
                             , getCallGraph
                             , functions
                             , calls
                             , calledBy
                             , nameLevels
                             , reachable ) where

import qualified G2.Language.ExprEnv as E
import G2.Language.Naming
import G2.Language.Syntax

import Data.Graph hiding (reachable)
import qualified Data.Graph as G
import qualified Data.HashMap.Lazy as M
import Data.Maybe

import Debug.Trace

data CallGraph = CallGraph { graph :: Graph
                           , nfv :: Vertex -> ((), Name, [Name])
                           , vert :: Name -> Maybe Vertex}

getCallGraph :: E.ExprEnv -> CallGraph
getCallGraph eenv =
    let
        funcs = E.keys eenv
    
        (g, nfv', vert') = graphFromEdges
            . map (\(n, e) -> 
                        let
                            calls = filter (\n -> n `elem` funcs) . map idName $ varIds e
                        in
                        ((), n, calls)) $ E.toList eenv
    in
    CallGraph g nfv' vert'

functions :: CallGraph -> [Name]
functions cg = map (\(_, n, _) -> n) . map (nfv cg) . vertices $ graph cg

callsList :: CallGraph -> [(Name, Name)]
callsList cg = map (\(v1, v2) -> (mid $ nfv cg v1, mid $ nfv cg v2)) . edges $ graph cg
    where
        mid (_, m, _) = m

nodeName :: CallGraph -> Vertex -> Name
nodeName g v = (\(_, n, _) -> n) $ nfv g v

-- | Functions directly called by the named function
calls :: Name -> CallGraph -> Maybe [Name]
calls n g = fmap (\(_, _, ns) -> ns) . fmap (nfv g) $ vert g n

calledBy :: Name -> CallGraph -> [Name]
calledBy n g = map fst
             . filter ((==) n . snd)
             . map (\(v1, v2) -> (nodeName g v1, nodeName g v2)) $ edges (graph g)

-- Functions directly and indirectly called by the named function
reachable :: Name -> CallGraph -> [Name]
reachable n g =
    map ((\(_, x, _) -> x) . nfv g) . maybe [] (G.reachable $ graph g) $ vert g n

-- | Returns:
-- (1) a list of list of names, where the first list contains functions
-- that are not called by any functions (except themselves), and the nth list, n > 2,
-- includes functions called by functions in the (n - 1)th list.
nameLevels :: CallGraph -> [[Name]]
nameLevels cg =
    let
        fs = functions cg
        eds = callsList cg

        callers = fs
        called_by_others = mapMaybe (\(n1, n2) -> if n1 /= n2 then Just n2 else Nothing) eds

        only_caller = filter (`notElem` called_by_others) callers
    in
    only_caller:nameLevels' only_caller (removeEdgesTo only_caller eds)

nameLevels' :: [Name] -> [(Name, Name)] -> [[Name]]
nameLevels' [] _ = []
nameLevels' callers eds =
    let
        called = map snd $ filter (\(n1, _) -> n1 `elem` callers) eds
    in
    called:nameLevels' called (removeEdgesTo called eds)

removeEdgesTo :: [Name] -> [(Name, Name)] -> [(Name, Name)]
removeEdgesTo ns = filter (\(_, n2) -> n2 `notElem` ns)

-- nameLevels :: [Name] -> CallGraph -> [[Name]]
-- nameLevels start (CallGraph { graph = g, nfv = f, vert = v }) =
--     nameLevels' . map (mapTree (f'. f)) $ dfs g (mapMaybe v start)
--     where
--         f' (_, n, _) = n

-- nameLevels' :: Forest Name -> [[Name]]
-- nameLevels' [] = []
-- nameLevels' frst = map nodeName frst:nameLevels' (concatMap nodeNested frst)
--     where
--         nodeName (Node n _) = n
--         nodeNested (Node _ ns) = ns

------------------------------------------
-- Helper functions

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f (Node x xs) = Node (f x) $ map (mapTree f) xs