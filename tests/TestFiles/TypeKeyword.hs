module TypeKeyword where

import Control.Monad
import Data.Char -- 1.3
import System.Environment

type Age = Int

yearPasses :: Age -> Age
yearPasses x = x + 1

-------------------------------------------------------------------------------

data PResult = POk
               | PFail
               deriving Eq

type Parser = Int -> Int -> PResult

pgAlts :: [Parser] -> Parser
pgAlts ps _ toks
   = let
        useAlts [] = POk
        useAlts (p:ps)
           = case p 0 toks of
                PFail -> useAlts []
                successful_parse -> successful_parse
     in
        useAlts ps

callAlts :: Parser
callAlts = pgAlts [ \_ _ -> POk ]