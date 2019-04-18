module G2.Translation.QuasiQuotes (g2) where

import G2.Language.Syntax

import Control.Monad.IO.Class

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import System.IO.Unsafe

g2 :: QuasiQuoter
g2 = QuasiQuoter { quoteExp = parseHaskellQ
                 , quotePat = error "g2: No QuasiQuoter for patterns."
                 , quoteType = error "g2: No QuasiQuoter for types."
                 , quoteDec = error "g2: No QuasiQuoter for declarations." }

parseHaskellQ :: String -> Q Exp
parseHaskellQ s = parseHaskellQ' s >>= liftData

parseHaskellQ' :: String -> Q Expr
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    return (Lit $ LitInt 54)