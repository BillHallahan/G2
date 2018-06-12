module G2.Internals.Language.Monad.Typing ( tyIntT
                                          , tyIntegerT
                                          , tyDoubleT
                                          , tyFloatT
                                          , tyBoolT ) where

import G2.Internals.Language.Syntax
import G2.Internals.Language.Support
import G2.Internals.Language.Typing

import G2.Internals.Language.Monad.Support


appKV :: ExState s m => (KnownValues -> a) -> m a
appKV f = do
    kv <- knownValues
    return $ f kv

tyIntT :: ExState s m => m Type
tyIntT = appKV tyInt

tyIntegerT :: ExState s m => m Type
tyIntegerT = appKV tyInteger

tyDoubleT :: ExState s m => m Type
tyDoubleT = appKV tyDouble

tyFloatT :: ExState s m => m Type
tyFloatT = appKV tyFloat

tyBoolT :: ExState s m => m Type
tyBoolT = appKV tyBool