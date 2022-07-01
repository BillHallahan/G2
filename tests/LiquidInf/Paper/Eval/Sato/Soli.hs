{-@ LIQUID "--no-termination" @-}

module Soli (main) where

data Peg = Out | Empty | Peg

print_peg :: Peg -> IO ()
print_peg Out = putStr ""
print_peg Empty = putStr " "
print_peg Peg = putStr "$"

print_board :: (Int -> Int -> Peg) -> IO ()
print_board board =
    mapM_ (\i -> do
                mapM (\j -> print_peg (board i j)) [0..8]
                putStr "\n") [0..8]

data Direction = Dir { dx :: Int, dy :: Int }

data Move =  Move { x1 :: Int, y1 :: Int, x2 :: Int, y2 :: Int }

solve :: Int -> Int -> (Int -> Int -> Peg) -> (Int -> Move) -> IO Bool
solve counter m board moves = do
    let dir i = [ Dir { dx = 0, dy = 1 }, Dir { dx = 1, dy = 0 }
                , Dir { dx = 0, dy = -1 }, Dir { dx = -1, dy = 0 }] !! i
        counter' = counter + 1
    if m == 31 then
        case board 4 4 of
            Peg -> return True
            Out -> return False
            Empty -> return False
    else do
        if counter' `mod` 2 == 0 then print counter'
            else return ()
        anyM (\i -> anyM (\j -> 
                case board i j of
                    Out -> return False
                    Empty -> return False
                    Peg -> do
                        anyM (\k -> do
                                    let d1 = dx (dir k)
                                        d2 = dy (dir k)
                                        i1 = i + d1
                                        i2 = i1 + d1
                                        j1 = j + d2
                                        j2 = j1 + d2 in
                                        case board i1 j1 of
                                            Out -> return False
                                            Empty -> return False
                                            Peg -> case board i2 j2 of
                                                        Out -> return False
                                                        Peg -> return False
                                                        Empty -> do
                                                            s <- solve counter' (m + 1) board moves
                                                            return s) [0..3])
                [1..7]) [1..7]


-- Helper
ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM b t f = do b <- b; if b then t else f

(||^) :: Monad m => m Bool -> m Bool -> m Bool
(||^) a b = ifM a (pure True) b

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM p = foldr ((||^) . p) (pure False)

solve_solitaire :: IO ()
solve_solitaire = do
    let board i j = ([
                      [ Out, Out, Out, Out, Out, Out, Out, Out, Out],
                      [ Out, Out, Out, Peg, Peg, Peg, Out, Out, Out],
                      [ Out, Out, Out, Peg, Peg, Peg, Out, Out, Out],
                      [ Out, Peg, Peg, Peg, Peg, Peg, Peg, Peg, Out],
                      [ Out, Peg, Peg, Peg, Empty, Peg, Peg, Peg, Out],
                      [ Out, Peg, Peg, Peg, Peg, Peg, Peg, Peg, Out],
                      [ Out, Out, Out, Peg, Peg, Peg, Out, Out, Out],
                      [ Out, Out, Out, Peg, Peg, Peg, Out, Out, Out],
                      [ Out, Out, Out, Out, Out, Out, Out, Out, Out]
                    ] !! i) !! j
        counter = 0
        moves i = Move {x1 = 0, y1 = 0, x2 = 0, y2 = 0}
    s <- solve counter 0 board moves
    if s then do putStr "\n"; print_board board else return ()

main :: IO ()
main = solve_solitaire
