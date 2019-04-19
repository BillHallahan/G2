{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module G2.Translation.QuasiQuotes (g2) where

import G2.Config
import G2.Interface.Interface
import G2.Language.Support
import G2.Language.Syntax
import G2.Translation.Interface
import G2.Translation.TransTypes

import Control.Monad.IO.Class

import qualified Data.HashMap.Lazy as HM
import qualified Data.Text as T
import Data.Typeable

import Language.Haskell.TH.Lib
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

import System.IO
import System.IO.Temp

import System.FilePath

g2 :: QuasiQuoter
g2 = QuasiQuoter { quoteExp = parseHaskellQ
                 , quotePat = error "g2: No QuasiQuoter for patterns."
                 , quoteType = error "g2: No QuasiQuoter for types."
                 , quoteDec = error "g2: No QuasiQuoter for declarations." }

parseHaskellQ :: String -> Q Exp
parseHaskellQ s = parseHaskellQ' s >>= dataToExpQ (\a -> liftText <$> cast a)
    where
        liftText txt = AppE (VarE 'T.pack) <$> lift (T.unpack txt)


parseHaskellQ' :: String -> Q Expr
parseHaskellQ' s = do
    ms <- reifyModule =<< thisModule
    runIO $ do
        print ms
        parseHaskellIO s

parseHaskellIO :: String -> IO Expr
parseHaskellIO str = do
    (_, exG2) <- withSystemTempFile "ThTemp.hs"
            (\filepath handle -> do
                hPutStrLn handle $ "module ThTemp where\ng2Expr = " ++ str
                hFlush handle
                hClose handle
                translateLoaded (takeDirectory filepath) filepath []
                    simplTranslationConfig mkConfigDef)
  
    let (s, is, b) = initState' exG2 "g2Expr" (Just "ThTemp") mkConfigDef

    let CurrExpr _ ce = curr_expr s 
    return ce
