module G2.Verify.StaticArgTrans where

import G2.Language

import Data.List
import Data.Maybe

data Static = Static | NonStatic
              deriving (Eq, Show, Read)

detStatic :: Name -- ^ Function name
          -> Expr -- ^ Function body
          -> [Static] -- ^ Whether each lambda bound argument is static
detStatic f e =
    let
        ns = map idName $ leadingLamIds e
        f_args = mapMaybe isF $ getFuncCalls e
        
        f_align = transpose f_args
    in
    zipWith (\n as -> if all (isSameArg n) as then Static else NonStatic) ns (f_align ++ repeat [])
    where
        isF e_ | Var (Id n_ _):es <- unApp e_
               , f == n_ = Just es
               | otherwise = Nothing
        
        isSameArg n (Var (Id vn _)) = n == vn
        isSameArg _ _ = False