module CallForHPC where

import qualified Control.Exception as Ex
import Data.Char
import Bernouilli
import Data.Ratio
import System.Environment
import Control.Monad


main_internal_g2 :: IO ()
main_internal_g2 =do
  Ex.try (print (main (2) (\fs'6 -> (\fs'4 -> case (case fs'4 of
       fs'2 -> case fs'2 == (1) of
            True  -> 0
            False  -> 1) of
      fs -> fs)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (2) (\fs'3 -> (\fs'2 -> case 0 of
      fs -> fs)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (2) (\fs'4 -> (\fs'6 -> case (case fs'4 of
       fs'2 -> case fs'2 == (4) of
            True  -> 0
            False  -> 1) of
      fs -> fs)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (2) (\fs'3 -> (\fs'2 -> case 0 of
      fs -> fs)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (1) (\_ -> (\_ -> 0)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (3) (\_ -> (\_ -> 0)))) :: IO (Either Ex.SomeException ())
  Ex.try (print (main (0) (\_ -> (\_ -> 0)))) :: IO (Either Ex.SomeException ())
  return ()
  