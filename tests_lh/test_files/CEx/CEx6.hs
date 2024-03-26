{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--prune-unsorted" @-}

module Combined ( List ) where

import Prelude hiding (length, replicate, foldr, foldr1, map, concat, zipWith, repeat)
import Data.List (minimumBy)
import qualified Data.Map as M

infixr 9 :+:

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:String | false} -> a @-}
die str = error ("Oops, I died!" ++ str)

data List a = Emp
            | (:+:) a (List a)
              deriving (Eq, Ord, Show)

{-@ measure size      :: List a -> Int
    size (Emp)        = 0
    size ((:+:) x xs) = 1 + size xs
  @-}

{-@ invariant {v:List a | 0 <= size v} @-}

foldr :: (a -> b -> b) -> b -> List a -> b
foldr _  b Emp        = b
foldr op b (x :+: xs) = x `op` foldr op b xs

-- | N-Dimensional Point
type Point   = List Double

{-@ distance :: Int
             -> (Combined.List {_ : GHC.Types.Double | false})
             -> {xs : (Combined.List GHC.Types.Double) | (size xs == 0)}
             -> GHC.Types.Double @-}
distance :: Int -> Point -> Point -> Double
distance n px py = sqrt $ foldr (+) 0 px

{-@ nearest :: n:Int
            -> (M.Map {c : Int | (c >= 0) } {xs : (List Double) | (size xs == n)})
            -> {ys : (List Double) | (size ys == n)}
            -> Int @-}
nearest   :: Int ->  M.Map Int Point -> Point -> Int
nearest n centers p = pSol
  where
    keyList = M.toList centers
    f x1 x2 = compare (distance n (snd x1) p) (distance n (snd x2) p)
    pSol    = minKeyFuncList keyList f

minKeyFuncList :: (Ord v) => [(k,v)] -> ((k,v) -> (k,v) -> Ordering) -> k
minKeyFuncList xs f = fst $ minimumBy f xs

