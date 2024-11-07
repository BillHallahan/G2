module STRef where

import Control.Monad.ST
import Data.STRef

f :: String
f = runST (do
        ref <- newSTRef "hello"
        x <- readSTRef ref
        writeSTRef ref (x ++ "world")
        readSTRef ref )
