-- There was a lot of discussion about various ways of computing
-- Bernouilli numbers (whatever they are) on haskell-cafe in March 2003
-- Here's one of the programs.

-- It's not a very good test, I suspect, because it manipulates big integers,
-- and so probably spends most of its time in GMP.

module Bernouilli where

import Data.Ratio
import System.Environment
import Control.Monad

-- powers = [[r^n | r<-[2..]] | n<-1..]
-- type signature required for compilers lacking the monomorphism restriction
powers :: [[Integer]]
powers = [2..] : map (zipWith (*) (head powers)) powers

-- powers = [[(-1)^r * r^n | r<-[2..]] | n<-1..]
-- type signature required for compilers lacking the monomorphism restriction
neg_powers :: [[Integer]]
neg_powers =
  map (zipWith (\n x -> if n then x else -x) (iterate not True)) powers

pascal:: [[Integer]]
pascal = [1,2,1] : map (\line -> zipWith (+) (line++[0]) (0:line)) pascal

bernoulli _ 0 = 1
bernoulli _ 1 = -(1%2)
bernoulli _ n | odd n = 0
bernoulli f n =
   (-1)%2
     -- SYMFUN: The following line makes use of symbolic function
     + sum [ fromIntegral ((sum $ zipWith f powers (tail $ tail combs)) -
                            fromIntegral k) %
             fromIntegral (k+1)
     | (k,combs)<- zip [2..n] pascal]
  where powers = (neg_powers!!(n-1))

{-main = replicateM_ 500 $ do
 arg <- mkSymbolic
 let n = (arg)::Int
 print (hash (show (bernoulli n)))-}

main arg symFun  =
  let n = (arg)::Int in
  bernoulli symFun n
