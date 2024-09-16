{-# LANGUAGE CPP #-}

module G2.Liquid.DataConSigs (createDCSigs) where

import G2.Language
import G2.Liquid.Conversion
import G2.Liquid.Types

import Language.Haskell.Liquid.Types

#if MIN_VERSION_GLASGOW_HASKELL(9,0,2,0)
import qualified GHC.Types.Var as Var
#else
import qualified Var as Var
#endif

import qualified Data.HashMap.Lazy as HM

createDCSigs :: [(Var.Var, LocSpecType)]  -> LHStateM ()
createDCSigs dcs = mapM_ (uncurry dcSig) dcs

dcSig :: Var.Var -> LocSpecType -> LHStateM ()
dcSig v lst = do
    let st = val lst
        is = undefined :: [Id]
        r = undefined :: Id
    dm <- dictMapFromIds is
    e <- convertAssertSpecType dm HM.empty is r st
    return ()