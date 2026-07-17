{-# LANGUAGE MultiWayIf #-}

module SeqNat where

-- CONFIG: --smt-adt Nat

data Nat = S Nat | Z deriving Eq

con :: [Nat] -> [Nat] -> [Nat]
con xs ys = if length xs > length ys
                    then xs ++ ys
                    else if length xs == length ys
                                then ys
                                else ys ++ xs

listLen :: [Nat] -> (Int, Bool)
listLen xs = let l = length xs in (l, case l > 5 of True -> False; False -> True)

listLen2 :: [Nat] -> (Int, Bool)
listLen2 s =
    case s of
        (c:s) ->
            let l = length (c:s) in
            if l > 4 then (l, True) else (l, False)
        [] -> (1000, False)
    
listLen3 :: Nat -> [Nat] -> (Int, Bool)
listLen3 c s =
    let l = length (c:s) in
    if l > 4 then (l, True) else (l, False)

listApp :: [Nat] -> [Nat] -> Int
listApp xs ys = let cs = xs ++ ys in
                if | cs == [Z, S Z, S (S Z)] -> 2
                   | cs == [S Z, Z] -> 1
                   | otherwise -> 0

take1 :: [Nat] -> (Bool, [Nat])
take1 str = case t == [S Z, Z, S (S Z), S Z, Z] of
                True -> (False, t)
                False -> (True, t)
    where
        t = take 5 str
