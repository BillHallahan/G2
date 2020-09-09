module G2.Execution.Zipper ( initZipper
                           , evalZipper 
                           , Counter
                           , Tree
                           , Status(..)) where

import Debug.Trace

------------
-- Execution is represented by a multiway tree. Initially it is just a `Root` that contains the initial state(s). In each function call, any `Leaf`
-- node (or a state from the `Root`) is picked and reduced, following which either:
--      (i) the node is replaced with new `Leaf` node(s) (new leaf node(s) are added).
--      (ii) if during reduction, execution branches into potentially mergeable states, the node is replaced with a `CaseSplit` node, and the
--      reduceds are added as `Leaf` nodes. A `mergePtFrame` is added to each reduced's exec_stack, and the Counter is incremented.
--      (iii) if during reduction a `mergePtFrame` is encountered on the exec_stack, the node is replaced with a `ReadyToMerge` node
-- A `ReadyToMerge` node may also be picked, in which case it is merged with its siblings if possible, else any sibling that is a `Leaf` node is
-- picked for reduction next.

data Status = WorkNeeded | WorkSaturated | Split | Mergeable | Accept | Discard

type Counter = Int
data Tree a = CaseSplit [Tree a] -- Node corresponding to point at which execution branches into potentially mergeable states
            | Leaf a Counter
            | ReadyToMerge a Counter -- 'a's can be merged if they are all ReadyToMerge nodes with same parent and Counter

-- List of (Parent, [sibling]) pairs that represents path from a Node to the Root. Enables traversal from the node to the rest of the tree
-- See: https://wiki.haskell.org/Zipper
newtype Cxt a = Cxt [(Tree a, [Tree a])]
type Zipper a = (Tree a, Cxt a)

data ZipperTree a b = ZipperTree { zipper :: Zipper a -- ^ Zipper on a tree of a-s
                                 , env :: b -- ^ Values that might be needed for reduction
                                 , work_func :: a -> b -> IO ([a], b, Status) -- ^ Function to perform work on an object
                                 , merge_func :: a -> a -> b -> IO (Maybe a, b) -- ^ Func to merge objects at specified idx
                                 , reset_merging_func :: a -> a }

-- | Creates a Zipper of a Tree with just one node
initZipper :: a -> b
           -> (a -> b -> IO ([a], b, Status))
           -> (a -> a -> b -> IO (Maybe a, b))
           -> (a -> a)
           -> ZipperTree a b
initZipper s e workFn mergeFn resetMergFn =
    let root = CaseSplit [Leaf s 0]
        zipr = (root, Cxt [])
    in ZipperTree { zipper = zipr
                  , env = e
                  , work_func = workFn
                  , merge_func = mergeFn
                  , reset_merging_func = resetMergFn }

evalZipper :: ZipperTree a b -> IO (b)
evalZipper zipTree@(ZipperTree { zipper = zipr
                              , env = e
                              , work_func = workFn
                              , merge_func = mergeFn
                              , reset_merging_func = resetMergFn })
    | CaseSplit s <- fst zipr = do
        case s of
            [] -> return e
            (x:xs) -> do
                assertConsistent "CaseSplit 1" zipr
                let leaf = x
                    root' = CaseSplit xs
                    zipr' = (leaf, Cxt [(root', xs)])
                assertConsistent "CaseSplit 2" zipr'
                evalZipper (zipTree { zipper = zipr' })
    | Leaf x count <- fst zipr = do
        assertConsistent "Leaf" zipr
        (as, e', status) <- workFn x e        
        case status of
            Accept -> do
                let zipr' = deleteNode zipr -- set zipper to sibling, or a sibling of any of its parents, remove this from children of parent
                assertConsistent "Leaf Accept" zipr'
                evalZipper (zipTree { zipper = zipr', env = e' })
            Discard -> do
                let zipr' = deleteNode zipr
                assertConsistent "Leaf Discard" zipr'
                evalZipper (zipTree { zipper = zipr', env = e' })
            Mergeable -> do
                let tree' = ReadyToMerge (head as) (count - 1) -- redRules only returns 1 state when status is Mergeable
                    zipr' = (tree', snd zipr)
                assertConsistent "Leaf Mergeable" zipr'
                evalZipper (zipTree { zipper = zipr', env = e' })
            WorkSaturated -> do
                -- do not add reduced states to current tree. Instead add to list of states in root.
                -- prevents tree from growing to deep. We do not attempt to merge these states
                let reduceds = map resetMergFn as -- remove any merge pts
                    zipr' = floatReducedsToRoot zipr reduceds
                    zipr'' = deleteNode zipr'
                assertConsistent "Leaf WorkSaturated 1" zipr'
                assertConsistent "Leaf WorkSaturated 2" zipr''
                evalZipper (zipTree { zipper = zipr'', env = e' })
            Split -> do
                let leaves = map (\a -> Leaf a (count + 1)) as
                    tree' = CaseSplit leaves
                    zipr' = (tree', snd zipr) -- replace node with CaseSplit node and leaves as children
                    zipr'' = pickChild zipr'
                assertConsistent "Leaf Split" zipr''
                evalZipper (zipTree { zipper = zipr'', env = e' })
            WorkNeeded -> do
                let leaves = map (\a -> Leaf a count) as 
                    zipr' = replaceNode zipr leaves -- replace node with leaves
                assertConsistent "Leaf WorkNeeded" zipr'
                evalZipper (zipTree { zipper = zipr', env = e' })
    | ReadyToMerge x count <- fst zipr = do
        let siblings = getSiblings zipr
        if allReadyToMerge siblings count
            then do
                (mergedStates, e') <- mergeObjsZipper mergeFn (x:(map treeVal siblings)) e
                let leaves = map (\a -> Leaf a count) mergedStates
                    zipr' = replaceParent zipr leaves
                assertConsistent "ReadyToMerge" zipr'
                evalZipper (zipTree { zipper = zipr', env = e' })
            else do
                let zipr' = pickSibling zipr
                assertConsistent "ReadyToMerge" zipr'
                evalZipper (zipTree { zipper = zipr', env = e })
    | otherwise = error "Should not reach this case"

allReadyToMerge :: [Tree a] -> Counter -> Bool
allReadyToMerge leaves count = all (isReadyToMerge count) leaves

isReadyToMerge :: Counter -> Tree a -> Bool
isReadyToMerge count (ReadyToMerge _ c) = c == count
isReadyToMerge _ _ = False

treeVal :: Tree a -> a
treeVal (ReadyToMerge val _) = val
treeVal (Leaf val _) = val
treeVal _ = error "Tree has no value"

getSiblings :: Zipper a -> [Tree a]
getSiblings (_, context) =
    case context of
        Cxt (x:_) -> snd x
        _ -> []

getParent :: Zipper a -> Maybe (Tree a)
getParent (_, context) =
    case context of
        Cxt (x:_) -> Just (fst x)
        _ -> Nothing

getChildren :: Tree a -> [Tree a]
getChildren z =
    case z of
        CaseSplit st -> st
        Leaf _ _ -> []
        ReadyToMerge _ _ -> []

assertConsistent :: String -> Zipper a -> IO ()
assertConsistent s z
    = return ()
    -- | Just par <- getParent z =
    --     let
    --         num_children = length (getChildren par)
    --         num_siblings = length (getSiblings z)
    --     in
    --     case num_children == num_siblings + 1 of
    --         True -> return ()
    --         False -> error $ "inconsistent zipper at " ++ s
    --                             ++ "\nnum_par_children = " ++ show num_children
    --                             ++ "\nnum_siblings = " ++ show num_siblings
    -- | otherwise =
    --     case length (getSiblings z) == 0 of
    --         True -> return ()
    --         False -> error $ "siblings at root at " ++ s

-- | Add the reduceds to the list of states to be processed in the root of the treeZipper tz
floatReducedsToRoot :: Zipper a -> [a] -> Zipper a
floatReducedsToRoot tz@(t, (Cxt (c:[]))) reduceds =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        Just (CaseSplit st) ->
            let
                parent' = CaseSplit (st ++ map (flip Leaf 0) reduceds)
            in
            (t, Cxt $ (parent', siblings):[])
        _ -> error "not supported"
floatReducedsToRoot tz@(t, (Cxt (_:cs))) reduceds =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        (Just j_par) ->
            let
                parentZipper = (j_par, Cxt cs)
                (parent', Cxt context') = floatReducedsToRoot parentZipper reduceds
            in
            (t, Cxt $ (parent', siblings):context')

-- | Replace current node with new leaves (if parent is CaseSplit), and focus on a new leaf, if any. If parent is root, add to list
replaceNode :: Zipper a -> [Tree a] -> Zipper a
replaceNode tz@(_, (Cxt  (c:[]))) leaves =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        Just (CaseSplit st) -> (CaseSplit (leaves ++ st), Cxt [])
        _ -> error "No other tree can be parent"
replaceNode tz@(_, (Cxt (_:cs))) leaves =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        Just (CaseSplit st) ->
            let
                parent' = CaseSplit (leaves ++ siblings)
            in
            pickChild (parent', Cxt cs)
        _ -> error "No other tree can be parent"

-- | Replace parent with new leaves (if parent of parent is CaseSplit). If parent of parent is Root, add to list
replaceParent :: Zipper a -> [Tree a] -> Zipper a
replaceParent tz@(_, (Cxt context)) leaves =
    let
        parent = getParent tz
    in
    case parent of
        Just j_par ->
            let
                zipper' = (j_par, Cxt (drop 1 context)) -- losing information about current siblings, if any
            in
            replaceNode zipper' leaves

-- | Remove current tree from parent's list of children, and progressively move up, pruning any parent that has 0 children. 
-- Set zipper to focus on sibling (if any)
deleteNode :: Zipper a -> Zipper a
deleteNode tz@(_, (Cxt (c:[]))) =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        Just (CaseSplit st) -> (CaseSplit st, Cxt [])
        _ -> error "No other Tree can be a parent"
deleteNode tz@(_, (Cxt (_:cs))) =
    let
        parent = getParent tz
        siblings = getSiblings tz
    in
    case parent of
        Just j_par@(CaseSplit _) ->
            case siblings of
                l:ls ->
                    let
                        j_par' = CaseSplit siblings
                    in
                    (l, Cxt $ (j_par', ls):cs)
                [] -> deleteNode (j_par, Cxt cs)
        _ -> error "No other Tree can be a parent"

pickChild :: Zipper a -> Zipper a
pickChild tz@(t, (Cxt context))
    | CaseSplit leaves <- t =
        case leaves of
            l:ls -> (l, Cxt $ (t, ls):context)
            [] -> deleteNode tz
    | otherwise = error "No children to choose from"

-- | Pick a sibling that is not ReadyToMerge, if any
pickSibling :: Zipper a -> Zipper a
pickSibling tz@(t, (Cxt (_:cs))) =
    let
        siblings = getSiblings tz
        parent = getParent tz
        (siblings', sibling) = pickSibling' [] siblings
    in
    case parent of
        Just j_par -> (sibling, Cxt $ (j_par, t:siblings'):cs)
        Nothing -> error "pickSibling:No siblings"

pickSibling' :: [Tree a] -> [Tree a] -> ([Tree a],Tree a)
pickSibling' seen (x:xs) =
    case x of
        (Leaf _ _) -> (seen ++ xs, x)
        _ -> pickSibling' (x:seen) xs
pickSibling' _ [] = error "pickSibling must be called with at least one Tree that is a leaf"

-- Iterates through list and attempts to merge adjacent objects if possible. Does not consider all possible combinations
-- because number of successful merges only seem to increase marginally in such a case
mergeObjsZipper :: (a -> a -> b -> IO (Maybe a, b)) -> [a] -> b -> IO ([a], b)
mergeObjsZipper mergeFn (x1:x2:xs) e = do
    mrg <- mergeFn x1 x2 e
    case mrg of
        (Just exS, e') -> mergeObjsZipper mergeFn (exS:xs) e'
        (Nothing, e') -> do
            (merged, e'') <- mergeObjsZipper mergeFn (x2:xs) e'
            return (x1:merged, e'')
mergeObjsZipper _ ls e = return (ls, e)

-- | Similar to mergeObjsZipper, but considers all possible combinations when merging objects
-- mergeObjsAllZipper :: (a -> a -> b -> (Maybe a, b))
--                      -> [a] -> b
--                      -> ([a], b)
-- mergeObjsAllZipper mergeFn (x:xs) e =
--     let (done, rest, e') = mergeObjsAllZipper' mergeFn x [] xs e
--         (mergedStates, e'') = mergeObjsAllZipper mergeFn rest e'
--     in (done:mergedStates, e'')
-- mergeObjsAllZipper _ [] e = ([], e)

-- mergeObjsAllZipper' :: (a -> a -> b -> (Maybe a, b))
--                       -> a -> [a] -> [a] -> b
--                       -> (a, [a], b)
-- mergeObjsAllZipper' mergeFn x1 checked (x2:xs) e =
--     case mergeFn x1 x2 e of
--         (Just exS, e') -> mergeObjsAllZipper' mergeFn exS checked xs e'
--         (Nothing, e') -> mergeObjsAllZipper' mergeFn x1 (x2:checked) xs e'
-- mergeObjsAllZipper' _ x1 checked [] e = (x1, checked, e)
