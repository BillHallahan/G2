module CallForHPC where

import qualified Control.Exception as Ex
import Data.Char
import Main2
import Control.Monad
import System.Environment
import Data.Char


main_internal_g2 :: IO ()
main_internal_g2 =do
  Ex.try (print (main (\_ -> (\_ -> 1)) (\_ -> 0) [] [])) :: IO (Either Ex.SomeException ())
  return ()
  