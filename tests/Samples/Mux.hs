module Mux where

import Data.List

type Bit             =  Bool
  
mux                  :: [Bit] -> [[Bit]] -> [Bit]
mux sel xs           =  map (tree (||))
                     $  transpose
                     $  zipWith (\s x -> map (s &&) x) sel xs

tree                 :: (a -> a -> a) -> [a] -> a
tree f [x]           =  x
tree f (x:y:ys)      =  tree f (ys ++ [f x y])

decode               :: [Bit] -> [Bit]
decode []            =  [True] 
decode [x]           =  [not x,x]
decode (x:xs)        =  concatMap (\y -> [not x && y,x && y]) rest
  where
    rest             =  decode xs
  
binaryMux            :: [Bit] -> [[Bit]] -> [Bit]
binaryMux sel xs     =  mux (decode sel) xs

num                  :: [Bool] -> Int
num []               =  0
num (a:as)           =  (if a then 1 else 0) + 2 * num as

encode as            =  enc (as ++ replicate n False)
  where
    n                =  2 ^ ulog2 (length as) - length as

enc [_]              =  []
enc as               =  zipWith (||) (enc ls) (enc rs) ++ [tree (||) rs]
  where
    (ls, rs)         =  splitAt (length as `div` 2) as

oneHot []            =  False
oneHot (a:as)        =  if a then not (or as) else oneHot as


log2 :: Int -> Int
log2 n               =  if n == 1 then 0 else 1 + log2 (n `div` 2)

ulog2 n              =  log2 (2*n - 1)

-- Properties

infixr 0 -->
False --> _ = True
True --> x = x

prop_encode as = oneHot as --> (num (encode as) == n)
  where
    n = length (takeWhile not as)

prop_mux (sel, xs) =
      oneHot sel
  &&  length sel == length xs
  &&  all ((== length (head xs)) . length) xs
  --> mux sel xs == xs !! n
  where
    n = length (takeWhile not sel)

prop_encDec as = encode (decode as) == as
