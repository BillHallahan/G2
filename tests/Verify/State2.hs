
module State2 where

import Control.Applicative
import Control.Monad
import Data.Coerce

data Identity = Identity { runIdentity :: Int }

mapId :: (Int -> Int) -> Identity -> Identity
mapId f (Identity x) = Identity (f x)

data State = StateT { runStateT :: Int -> Identity }

runState :: State
         -> Int
         -> Int
runState m = runIdentity . runStateT m

mapSt :: (Int -> Int) -> State -> State
mapSt f (StateT m) = StateT (\ s ->
        mapId (\a -> f a) (m s))

p1 :: (Int -> Int) -> (Int -> Int) -> State -> Bool
p1 f g xs = runState (mapSt (f . g) xs) 0 == runState ((mapSt f . mapSt g) xs) 0
