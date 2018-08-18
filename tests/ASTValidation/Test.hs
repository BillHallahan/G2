-- | Unit testing file for ASTVerify which ensures that the functions are flagging errors and
-- returning results as expected 

module Main (main) where

import Test.HUnit
import G2.Internals.Language.ASTVerify
import G2.Internals.Language.Syntax
import Data.Text

letsTypeValidNoError :: Test
letsTypeValidNoError = TestCase (assertBool "Valid Let Failed"
  ([] == letsTypeValid (
      Let [ 
          ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitInt, Lit (LitInt 1))
      ]
      (Lit (LitChar 'c'))
      )))

letsTypeValidOneError :: Test
letsTypeValidOneError = TestCase (assertBool "Invalid Let Passed"
  ([] == letsTypeValid (
      Let [ 
          ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitChar, Lit (LitInt 1))
      ]
      (Lit (LitChar 'c'))
      )))

main :: IO Counts
main = runTestTT (TestList [
                     (TestLabel "Lets Bindings No Error" letsTypeValidNoError),
                     (TestLabel "Lets Bindings Char-Int Error" letsTypeValidOneError)
                       ])

  
-- Let one_error =
--       letsTypeValid (
--       Let
--       [
--         ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitChar, Lit (LitInt 1))
--       ]
--       (Lit (LitChar 'c'))
--       )

-- let multiple_errors =
--       letsTypeValid (
--       Let
--       [
--         ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitChar, Lit (LitInt 1)),
--         ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitChar, Lit (LitChar 'a')),
--         ((Id (Name (pack "integerId") (Just (pack "")) 0 Nothing)) TyLitInt, Lit (LitChar 'a')
--       ]
--       (Lit (LitChar 'c'))
--       )

-- let realTestOne = TyFun (
--   TyConApp (
--       Name (pack "List") (Just (pack "List")) 8214565720323870651
--                  (Just (Span {
--                          start = Loc {line = 58, col = 1, file = "./tests/Liquid/List.lhs"},
--                          end = Loc {line = 60, col = 48, file = "./tests/Liquid/List.lhs"}
--                          })))
--     [TyConApp (Name (pack "$") (Just $ pack "GHC.Tuple") 0 Nothing)
--       [TyConApp (Name (pack "Int") (Just $ pack "GHC.Types") 8214565720323815569 Nothing) [],
--        TyConApp (Name (pack "Int") (Just $ pack "GHC.Types") 8214565720323815569
--                  (Just (Span {start = Loc {line = 17, col = 1, file = "./base-4.9.1.0/GHC/Types2.hs"},
-- end = Loc {line = 17, col = 19, file = "./base-4.9.1.0/GHC/Types2.hs"}}))) []]])
--   (TyFun (TyConApp
--     (Name (pack "List") (Just $ pack "List") 8214565720323870651
--      (Just (Span {start = Loc {line = 58, col = 1, file = "./tests/Liquid/List.lhs"},
--                   end = Loc {line = 60, col = 48, file = "./tests/Liquid/List.lhs"}})))
--      [TyConApp (Name (pack "$") (Just $ pack "GHC.Tuple") 0 Nothing)
--       [TyConApp (Name (pack "Int") (Just $ pack "GHC.Types") 8214565720323815569 Nothing) [],
--        TyConApp (Name (pack "Int") (Just (pack "GHC.Types")) 8214565720323815569
--                  (Just (Span {start = Loc {line = 17, col = 1, file = "./base-4.9.1.0/GHC/Types2.hs"},
--                               end = Loc {line = 17, col = 19, file = "./base-4.9.1.0/GHC/Types2.hs"}
--                              }))) []]]
--    ) (TyConApp (Name (pack "Bool") (Just (pack "GHC.Types")) 0 Nothing) []))
