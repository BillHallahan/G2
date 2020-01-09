{-# LANGUAGE OverloadedStrings #-}

module G2.Execution.LogZipper ( initZipper
                              , evalZipper
                              , Counter
                              , Tree(..)) where

import qualified Data.Array as A
import qualified Data.Array.ST as AS
import qualified Data.Map as M
import Data.Maybe
import Data.List
import qualified Data.Set as S
import System.Directory

import qualified G2.Execution.WorkGraph as WG

------------
-- Execution is represented by a multiway tree. Initially it is just a `Root` that contains the initial state(s). In each function call, any `Leaf`
-- node (or a state from the `Root`) is picked and reduced, following which either:
--      (i) the node is replaced with new `Leaf` node(s) (new leaf node(s) are added).
--      (ii) if during reduction, execution branches into potentially mergeable states, the node is replaced with a `CaseSplit` node, and the
--      reduceds are added as `Leaf` nodes. A `mergePtFrame` is added to each reduced's exec_stack, and the Counter is incremented.
--      (iii) if during reduction a `mergePtFrame` is encountered on the exec_stack, the node is replaced with a `ReadyToMerge` node
-- A `ReadyToMerge` node may also be picked, in which case it is merged with its siblings if possible, else any sibling that is a `Leaf` node 
-- is picked for reduction next.

data Obj a = Obj { value :: a
                 , idx :: Int -- its 'timestamp' in the order of evaluation of the Tree
                 , level :: Int -- level in tree
                 , parents :: [Int] -- indices of parents, (from merge or split)
                 , children :: [Int]
                 , predecessor :: Maybe Int -- index of previous Obj (from a normal reduction)
                 , successor :: Maybe [Int] }

type Counter = Int

data Tree a = CaseSplit [Tree a] -- Node corresponding to point at which execution branches into potentially mergeable states
            | Leaf (Obj a) Counter
            | ReadyToMerge (Obj a) Counter -- 'a's can be merged if they are all ReadyToMerge nodes with same parent and Counter
            | Root [Obj a] (Tree a) -- list of a's to process, and 1 child
            | Empty

-- List of (Parent, [sibling]) pairs that represents path from a Node to the Root. Enables traversal from the node to the rest of the tree
-- See: https://wiki.haskell.org/Zipper
newtype Cxt a = Cxt [(Tree a, [Tree a])]

type Zipper a = (Tree a, Cxt a)

data ZipperTree a b = ZipperTree { zipper :: Zipper a -- ^ Zipper on a tree of a-s
                                 , env :: b -- ^ Values that might be needed for reduction
                                 , curr_idx :: Int -- ^ Used to assign 'timestamps' to new nodes
                                 , work_func :: a -> b -> IO ([a], b, WG.Status) -- ^ Function to perform work on an object
                                 , merge_func :: a -> a -> b -> (Maybe a, b) -- ^ Func to merge objects at specified idx
                                 , log_work_func :: a -> b -> String -- ^ Print object
                                 , reset_merging_func :: a -> a }

-- Data Structures for logging
-- ZipperTree contains a zipper to a tree that constantly grows and shrinks as objects are worked on or merged,the TreeLog below 
-- contains a tree that only grows, comprising every single Obj ever worked on
data ForestLog a = ForestLog { trees :: [TreeLog a]
                             , current :: TreeLog a }

newtype TreeLog a = TreeLog { nodes :: M.Map Int (Obj a)} -- map from idx of Obj to Obj

createObj :: a -> Int -> Int -> [Int] -> [Int] -> Maybe Int -> Maybe [Int] -> Obj a
createObj val i lvl par chil pre suc = Obj { value = val, idx = i, level = lvl, parents = par, children = chil
                                           , predecessor = pre, successor = suc }

fstObj :: a -> Obj a
fstObj val = createObj val 0 0 [] [] Nothing Nothing

-- | Creates a Zipper of a Tree with just one node
initZipper :: a -> b
           -> (a -> b -> IO ([a], b, WG.Status))
           -> (a -> a -> b -> (Maybe a, b))
           -> (a -> a)
           -> (a -> b -> String)
           -> ZipperTree a b
initZipper s e workFn mergeFn resetMergFn logWorkFn =
    let root = Root [fstObj s] Empty
        zipr = (root, Cxt [])
    in ZipperTree { zipper = zipr
                  , env = e
                  , curr_idx = 1
                  , work_func = workFn
                  , merge_func = mergeFn
                  , log_work_func = logWorkFn
                  , reset_merging_func = resetMergFn }

evalZipper :: ZipperTree a b -> IO (b)
evalZipper zipTree = do
    (res, logF) <- evalZipper' zipTree forestLog
    outputLog logF
    return res
    where
        forestLog = initForestLog
        evalZipper' zipT logF = do
            (zipT', newNodes, continue) <- step zipT
            -- mapM_ (outputVal (log_work_func zipT') "test" (env zipT')) newNodes
            let logF' = logVal logF newNodes
            case continue of
                False -> do -- (putStrLn $ DM.showTreeWith (\k x -> show (k, idx x)) True False (nodes . current $ logF'))
                            return (env zipT', logF')
                True -> evalZipper' zipT' logF'

step :: ZipperTree a b -> IO (ZipperTree a b, [Obj a], Bool)
step zipTree@(ZipperTree { zipper = zipr, env = e, curr_idx = i, work_func = workFn, merge_func = mergeFn
                         , reset_merging_func = resetMergFn })
    | Root s _ <- fst zipr = case s of
        [] -> return (zipTree, [], False)
        (x:xs) -> do
            let leaf = Leaf x 0
                root' = Root xs leaf
                zipr' = (leaf, Cxt [(root', [])])
            return (zipTree { zipper = zipr' }, [], True)
    | Leaf obj@(Obj { idx = prevIdx, level = prevLvl}) count <- fst zipr = do
        (as, e', status) <- workFn (value obj) e
        case status of
            WG.Accept -> do
                let zipr' = deleteNode zipr -- set zipper to sibling, or a sibling of any of its parents, remove this from children of parent
                return (zipTree { zipper = zipr', env = e' }, [], True)
            WG.Discard -> do
                let zipr' = deleteNode zipr
                return (zipTree { zipper = zipr', env = e' }, [], True)
            WG.Mergeable -> do
                let obj' = Obj {value = head as, idx = i, level = prevLvl, parents = [], children = []
                               , predecessor = Just prevIdx, successor = Nothing}
                let tree' = ReadyToMerge obj' (count - 1) -- redRules only returns 1 state when status is Mergeable
                    zipr' = (tree', snd zipr)
                    i' = i + 1
                return (zipTree { zipper = zipr', env = e', curr_idx = i' }, [obj'], True)
            WG.WorkSaturated -> do
                -- do not add reduced states to current tree. Instead add to list of states in root.
                -- prevents tree from growing to deep. We do not attempt to merge these states
                let reduceds = map resetMergFn as -- remove any merge pts
                    (i', reducedObjs) = mapAccumL (\newIdx a
                        -> (newIdx + 1, createObj a newIdx prevLvl [] [] (Just prevIdx) Nothing)) i reduceds
                    zipr' = floatReducedsToRoot zipr reducedObjs
                    zipr'' = deleteNode zipr'
                return (zipTree { zipper = zipr'', env = e', curr_idx = i' }, reducedObjs, True)
            WG.Split -> do
                let (i', objs) = mapAccumL (\newIdx a -> (newIdx + 1, createObj a newIdx (prevLvl + 1) [prevIdx] [] Nothing Nothing)) i as
                    leaves = map (\ob -> Leaf ob (count + 1)) objs
                    tree' = CaseSplit leaves
                    zipr' = (tree', snd zipr) -- replace node with CaseSplit node and leaves as children
                    zipr'' = pickChild zipr'
                return (zipTree { zipper = zipr'', env = e', curr_idx = i'}, objs, True)
            WG.WorkNeeded -> do
                let (i', objs) = mapAccumL (\newIdx a -> (newIdx + 1, createObj a newIdx prevLvl [] [] (Just prevIdx) Nothing)) i as
                    leaves = map (\ob -> Leaf ob count) objs
                    zipr' = replaceNode zipr leaves -- replace node with leaves
                return (zipTree { zipper = zipr', env = e', curr_idx = i'}, objs, True)
    | ReadyToMerge (Obj {value = x, idx = prevIdx, level = prevLvl}) count <- fst zipr = do
        let siblings = getSiblings zipr
        if allReadyToMerge siblings count
            then do
                let (mergedStates, e') = mergeObjsZipper mergeFn (x:(map (value . treeVal) siblings)) e
                    (i', objs) = mapAccumL (\newIdx a
                        -> (newIdx + 1, createObj a newIdx (prevLvl + 1) [prevIdx] [] Nothing Nothing)) i mergedStates
                    leaves = map (\ob-> Leaf ob count) objs
                    zipr' = replaceParent zipr leaves
                return (zipTree { zipper = zipr', env = e', curr_idx = i' }, objs, True)
            else do
                let zipr' = pickSibling zipr
                return (zipTree { zipper = zipr', env = e }, [], True)
    | otherwise = error "Should not reach this case"

allReadyToMerge :: [Tree a] -> Counter -> Bool
allReadyToMerge leaves count = all (isReadyToMerge count) leaves

isReadyToMerge :: Counter -> Tree a -> Bool
isReadyToMerge count (ReadyToMerge _ c) = c == count
isReadyToMerge _ _ = False

treeVal :: Tree a -> Obj a
treeVal (ReadyToMerge val _) = val
treeVal (Leaf val _) = val
treeVal _ = error "Tree has no value"

getSiblings :: Zipper a -> [Tree a]
getSiblings (_, context) = case context of
    Cxt (x:_) -> snd x
    _ -> []

getParent :: Zipper a -> Tree a
getParent (_, context) = case context of
    Cxt (x:_) -> fst x
    _ -> error "No parent in this Cxt"

-- | Add the reduceds to the list of states to be processed in the root of the treeZipper tz
floatReducedsToRoot :: Zipper a -> [Obj a] -> Zipper a
floatReducedsToRoot tz@(t, (Cxt context)) reduceds =
    let parent = getParent tz
        siblings = getSiblings tz
    in case parent of
        Root st ch -> let parent' = Root (st ++ reduceds) ch
                      in (t, Cxt $ (parent', siblings):(drop 1 context))
        _ -> let parentZipper = (parent, Cxt (drop 1 context))
                 (parent', Cxt context') = floatReducedsToRoot parentZipper reduceds
             in (t, Cxt $ (parent', siblings):context')

-- | Replace current node with new leaves (if parent is CaseSplit), and focus on a new leaf, if any. If parent is root, add to list
replaceNode :: Zipper a -> [Tree a] -> Zipper a
replaceNode tz@(_, (Cxt context)) leaves =
    let parent = getParent tz
        siblings = getSiblings tz
    in case parent of
        Root st _ -> let newSt = (map treeVal leaves)
                     in (Root (newSt ++ st) Empty, Cxt [])
        CaseSplit _ -> let parent' = CaseSplit (leaves ++ siblings)
                        in pickChild (parent', Cxt (drop 1 context))
        _ -> error "No other tree can be parent"

-- | Replace parent with new leaves (if parent of parent is CaseSplit). If parent of parent is Root, add to list
replaceParent :: Zipper a -> [Tree a] -> Zipper a
replaceParent tz@(_, (Cxt context)) leaves =
    let parent = getParent tz
        zipper' = (parent, Cxt (drop 1 context)) -- losing information about current siblings, if any
    in replaceNode zipper' leaves

-- | Remove current tree from parent's list of children, and progressively move up, pruning any parent that has 0 children.
-- Set zipper to focus on sibling (if any)
deleteNode :: Zipper a -> Zipper a
deleteNode tz@(_, (Cxt context)) =
    let parent = getParent tz
        siblings = getSiblings tz
    in case parent of
        Root st _ -> (Root st Empty, Cxt [])
        CaseSplit _ -> case siblings of
            l:ls -> (l, Cxt $ (parent, ls):(drop 1 context))
            [] -> deleteNode (parent, Cxt (drop 1 context))
        _ -> error "No other Tree can be a parent"

pickChild :: Zipper a -> Zipper a
pickChild tz@(t, (Cxt context))
    | CaseSplit leaves <- t = case leaves of
        l:ls -> (l, Cxt $ (t, ls):context)
        [] -> deleteNode tz
    | otherwise = error "No children to choose from"

-- | Pick a sibling that is not ReadyToMerge, if any
pickSibling :: Zipper a -> Zipper a
pickSibling tz@(t, (Cxt context)) =
    let siblings = getSiblings tz
        parent = getParent tz
        (siblings', sibling) = pickSibling' [] siblings
    in (sibling, Cxt $ (parent, t:siblings'):(drop 1 context))

pickSibling' :: [Tree a] -> [Tree a] -> ([Tree a],Tree a)
pickSibling' seen (x:xs) = case x of
    (Leaf _ _) -> (seen++xs, x)
    _ -> pickSibling' (x:seen) xs
pickSibling' _ [] = error "pickSibling must be called with at least one Tree that is a leaf"

-- Iterates through list and attempts to merge adjacent objects if possible. Does not consider all possible combinations
-- because number of successful merges only seem to increase marginally in such a case
mergeObjsZipper :: (a -> a -> b -> (Maybe a, b))
                  -> [a] -> b
                  -> ([a], b)
mergeObjsZipper mergeFn (x1:x2:xs) e =
    case mergeFn x1 x2 e of
        (Just exS, e') -> mergeObjsZipper mergeFn (exS:xs) e'
        (Nothing, e') -> let (merged, e'') = mergeObjsZipper mergeFn (x2:xs) e'
                         in (x1:merged, e'')
mergeObjsZipper _ ls e = (ls, e)

-- | Similar to mergeObjsZipper, but considers all possible combinations when merging objects
mergeObjsAllZipper :: (a -> a -> b -> (Maybe a, b))
                     -> [a] -> b
                     -> ([a], b)
mergeObjsAllZipper mergeFn (x:xs) e =
    let (done, rest, e') = mergeObjsAllZipper' mergeFn x [] xs e
        (mergedStates, e'') = mergeObjsAllZipper mergeFn rest e'
    in (done:mergedStates, e'')
mergeObjsAllZipper _ [] e = ([], e)

mergeObjsAllZipper' :: (a -> a -> b -> (Maybe a, b))
                      -> a -> [a] -> [a] -> b
                      -> (a, [a], b)
mergeObjsAllZipper' mergeFn x1 checked (x2:xs) e =
    case mergeFn x1 x2 e of
        (Just exS, e') -> mergeObjsAllZipper' mergeFn exS checked xs e'
        (Nothing, e') -> mergeObjsAllZipper' mergeFn x1 (x2:checked) xs e'
mergeObjsAllZipper' _ x1 checked [] e = (x1, checked, e)

initForestLog :: ForestLog a
initForestLog = ForestLog { trees = [], current = initTreeLog }

initTreeLog :: TreeLog a
initTreeLog = TreeLog { nodes = M.empty }

-- print obj
outputVal :: (a -> b -> String) -> String -> b -> Obj a -> IO ()
outputVal logWorkFn dir e (Obj { idx = i, value = v }) = do
    let dir' = dir ++ "/"
    createDirectoryIfMissing True dir'

    let fn = dir' ++ "state" ++ (show i) ++ ".txt"
    let write = logWorkFn v e
    writeFile fn write

    putStrLn fn

-- build tree from new states created as evalZipper proceeds
logVal:: ForestLog a -> [Obj a] -> ForestLog a
logVal fl@(ForestLog { current = curr@(TreeLog { nodes = _nodes }) }) objs =
    let _nodes' = foldr (\obj@(Obj { idx = i, parents = ps, children = chldrn, predecessor = pre, successor = suc }) n ->
                        -- add Obj to map
                    let n' = M.insert i obj n
                        -- add Obj to parent's children
                        n'' = foldr (\parentIdx _n' -> M.adjust (\o@(Obj { children = c }) -> o {children = i:c}) parentIdx _n') n' ps
                        -- add Obj as childrens' parent
                        n''' = foldr (\childIdx _n' -> M.adjust (\o@(Obj { parents = p }) -> o {parents = i:p}) childIdx _n') n'' chldrn
                        -- add Obj to predecessor (if any) as a successor
                        n4 = case pre of
                            Just _pre -> M.adjust (\o@(Obj {successor = _suc}) -> 
                                o {successor = maybe (Just [i]) (\_sucs -> Just (i:_sucs)) _suc}) _pre n'''
                            Nothing -> n'''
                        -- add Obj to successors (if any) as a predecessor
                        n5 = case suc of
                            Just _suc -> foldr (\succIdx _n4
                                            -> M.adjust (\o@(Obj {predecessor = _pre}) -> o {predecessor = Just i}) succIdx _n4) n4 _suc
                            Nothing -> n4
                    in n5) _nodes objs
    in fl {current = curr { nodes = _nodes' }}

data Grid = Grid { canvas :: A.Array Int Char -- 2d grid represented as single array, with element (i,j) at index i*width + j
                 , width :: Int -- width of grid
                 , height :: Int -- height of grid
                 , depths :: M.Map Int Int -- current write depth of each level (i.e. top down)
                 , locations :: M.Map Int Int -- depth of each idx
                 , maxWidth :: Int -- number of digits of largest idx
                 , drawn :: S.Set Int } -- list of indices already drawn

outputLog :: ForestLog a -> IO ()
outputLog (ForestLog { current = curr@(TreeLog {nodes = _nodes}) }) = do
    let cHeight = (maybe 0 fst (M.lookupMax _nodes)) * 2
        cWidth = (3 + numDigits cHeight) * 40 -- width if all indices were written horizontally, with space in between
        c = createCanvas cHeight cWidth -- can possibly trim size by getting max level to make it more efficient in the future
        grid = Grid { canvas = c, width = cWidth, height = cHeight, depths = M.empty, locations = M.empty, drawn = S.empty
                    , maxWidth = 3 + numDigits cHeight }
        grid' = drawTree curr grid 1 -- very first node, '0', is not in tree
    printGrid grid'

drawTree :: TreeLog a -> Grid -> Int -> Grid
drawTree treeLog@(TreeLog { nodes = _nodes }) grid i
    | Just n <- M.lookup i _nodes =
        let grid' = drawNode treeLog grid n
            successors = successor n
            -- consecutively draw the subtrees from each successor onto the same grid
            grid'' = maybe grid' (foldr (\suc _grid -> drawTree treeLog _grid suc) grid') successors
            -- consecutively draw subtrees from each child
            grid''' = foldr (\child _grid -> drawTree treeLog _grid child) grid'' (children n)
        in grid'''
    | otherwise = grid

drawNode :: TreeLog a -> Grid -> Obj a -> Grid
drawNode (TreeLog { nodes = _nodes }) grid@(Grid {canvas = c, width = w, depths = d, drawn = prevDrawn, locations = locs
        , maxWidth = maxW}) o@(Obj {idx = i, level = l, parents = ps})
    | True <- S.member i prevDrawn = grid
    | otherwise =
        let lDepth = fromMaybe 0 (M.lookup l d) -- get and update depth at new level
            parentLvl = case ps of
                p:_ -> maybe l (\obj -> level obj) (M.lookup p _nodes)
                _ -> l
            parentDepth = case ps of
                p:_ -> fromMaybe 0 (M.lookup p locs)
                _ -> 0 -- ignore if no parent
            lDepth' = max (parentDepth + 1) (if parentLvl < l
                then (lDepth + 2)  -- keep blank in row above to separate prev seq
                else (lDepth + 1)) -- no need for blank row since parent is predecessor
            d' = foldr (\lvl -> M.insertWith (\oldDepth depth -> max depth oldDepth) lvl lDepth') d [0..l]
            locs' = M.insert i lDepth' locs

            posJ = 1 + (l * maxW)
            posI = lDepth'
            c' = writeStrToCanvas w (posI, posJ) (show i) c
            prevDrawn' = S.insert i prevDrawn

            -- draw line linking nodes from parentDepth to posI, in col posJ - 2, only if parentDepth > 0 (i.e. exists parent)
            -- and if parentLvl < l
            c'' = if parentDepth > 0 && parentLvl < l
                then drawConnectingLine w c' parentDepth posI (posJ - 2)
                else c'

        in {- trace ("i: " ++ (show i) ++ " children: " ++ show (children o)) $-} grid { canvas = c'', depths = d',
            drawn = prevDrawn', locations = locs' }

-- Create 2d grid of specified size with all spaces
createCanvas :: Int -> Int -> A.Array Int Char
createCanvas nrows ncols = AS.runSTArray $ do
    c <- AS.newArray (1, nrows * ncols) ' '
    return c

-- Insert string at specified position in canvas (1-indexed)
writeStrToCanvas :: Int -> (Int, Int) -> String -> A.Array Int Char -> A.Array Int Char
writeStrToCanvas wdth (i,j) str c = AS.runSTArray $ do
    c' <- AS.thaw c
    mapM_ (\((row, col), v) -> AS.writeArray c' (((row-1) * wdth) + col) v) (zip (zip (repeat i) [j..]) str)
    return c'

-- Draw a vertical line from `start` to `end` in column `col`, and two horizontal lines at either ends of vertical line
drawConnectingLine :: Int -> A.Array Int Char -> Int -> Int -> Int -> A.Array Int Char
drawConnectingLine wdth c start end col = AS.runSTArray $ do
    c' <- AS.thaw c
    AS.writeArray c' (((start-1) * wdth) + col-1) '-'
    AS.writeArray c' (((end-1) * wdth) + col+1) '-'
    mapM_ (\row -> AS.writeArray c' (((row-1) * wdth) + col) '|') [start..end]
    return c'

printGrid :: Grid -> IO ()
printGrid (Grid { canvas = c, width = w, height = h }) = mapM_ putStrLn [ map (\j -> c A.! (((i-1)*w) + j)) [1..w]| i <- [1..h]]

numDigits :: Int -> Int
numDigits x = length $ show x
