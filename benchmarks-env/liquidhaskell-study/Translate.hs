{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.IO.Class
import Data.Generics
import Data.List
import System.Environment

-- import GHC hiding (parseModule)
-- import GHC.Paths
-- import Digraph
-- import DynFlags
-- import FastString
-- import OccName
-- import Outputable
-- import qualified Parser as GHC
-- import RdrName

-- import Language.Haskell.GHC.ExactPrint
-- import Language.Haskell.GHC.ExactPrint.Parsers

import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc

-- main :: IO ()
-- main = do
--   [fp, func] <- getArgs
--   (anns, L l mod)  <- parseModule fp >>= \case
--     Right x -> return x
--     Left e -> error (show e)
--   let (wrap_mod, new_decls) = mkWrapper mod func
--   str <- withDynFlags (\d -> showPpr d wrap_mod)
--   Right (anns', m) <- withDynFlags (\d -> parseWith d fp GHC.parseModule str)
--   putStrLn $ exactPrint m (mergeAnns anns anns')
--   -- let (header, body) = break ("import" `isPrefixOf`) . lines $ exactPrint (L l wrap_mod) anns
--   -- putStrLn (unlines header)
--   -- putStrLn "import qualified Debug.Trace"
--   -- putStrLn (unlines body)
--   -- putStrLn "-- WRAPPER CODE"
--   -- mapM_ (putStrLn . showPpr unsafeGlobalDynFlags) new_decls

-- main = runGhc (Just libdir) $ do
--   df <- getDynFlags
--   setSessionDynFlags df
--   [fp, func] <- liftIO getArgs
--   addTarget =<< guessTarget fp Nothing
--   mg <- depanal [] True
--   let (ms:_) = reverse $ flattenSCCs (topSortModuleGraph False mg Nothing)
--   pm <- parseModule ms
--   let wpm = mkWrapper (unLoc (parsedSource pm)) func
--   df <- getDynFlags
--   liftIO $ putStrLn $ showPpr df wpm

-- mkWrapper :: HsModule RdrName -> String -> (HsModule RdrName, [LHsDecl RdrName])
-- mkWrapper mod func = (mod { hsmodDecls = wrapper : (everywhere (mkT tx_wrap)
--                                        $ everywhere (mkT tx_ty) (hsmodDecls mod))
--                          , hsmodImports = L (getLoc (head (hsmodDecls mod))) debug_trace_imp
--                                         : hsmodImports mod
--                          }, [wrapper] )
--   where
--   debug_trace_imp = (simpleImportDecl (mkModuleName "Debug.Trace")) { ideclQualified = True }

--   func_name = mkVarUnqual (fsLit func)

--   wrapped_name = mkVarUnqual . fsLit $ "wrapper_" ++ func

--   tx = tx_wrap `extT` tx_ty

--   tx_wrap (HsVar v)
--     | v == func_name
--     = HsVar wrapped_name
--   tx_wrap e
--     = e

--   -- TODO: args should be a list of argument names for the wrapper function.
--   -- generate from the definition of the actual function
--   args = case find (\fb -> func_name == unLoc (fun_id fb)) fun_binds of
--            Just fb -> map (mkVarUnqual . fsLit . (:[])) $
--                       take (matchGroupArity (fun_matches fb)) ['a' ..]
--            Nothing -> error ("could not find binder for: " ++ func)
--   fun_binds = [ d | ValD d@(FunBind {}) <- map unLoc $ hsmodDecls mod ]

--   -- TODO: ugh, have to replicate func's type, and add relevant Show constraints
--   -- to both.. (and possibly other functions (!) that call func)
--   -- - maybe instead we can drop *all* type sigs?
--   -- - possible problem there is that LH type will be too specific compared to inferred GHC type..
--   -- - probably worth a shot though...
--   -- wrapper_ty = undefined
--   tx_ty (TypeSig xs t p) = TypeSig xs (mkShow t) p
--   tx_ty sig              = sig

--   mkShow t = L l (mkQualifiedHsForAllTy show_ctxt t)
--     where
--     l = getLoc t
--     show_ctxt = L l (map show_ct tvs)
--     show_ct tv = L l (mkHsAppTys (L l (HsTyVar (Unqual (mkTcOcc "Show")))) [tv])

--     tvs = map (noLoc.HsTyVar) . nub $ listify (\name -> isRdrTyVar name) t

--   -- wrapper = noLoc (ValD (FunBind (noLoc wrapped_name)
--   --                                False
--   --                                (MG [noLoc (Match Nothing args Nothing [grhs])] (map (const PlaceHolder) args) PlaceHolder Generated)
--   --                                WpHole
--   --                                PlaceHolder
--   --                                []))
--   wrapper = L (getLoc . fun_id $ (head fun_binds)) (ValD (unLoc fun_bind))
--   fun_bind = mk_easy_FunBind
--                (UnhelpfulSpan (fsLit "fun_bind"))
--                wrapped_name
--                (map nlVarPat args)
--                body
--   -- grhs = GRHSs [noLoc (GHRS [] body)] EmptyLocalBinds
--   body = nlHsApps traceShowName [traced, payload]
--   traceShowName = mkRdrQual (mkModuleName "Debug.Trace") (mkVarOcc "traceShow")
--   traced = mkLHsTupleExpr $ nlHsLit (mkHsString func) : map nlHsVar args
--   payload = nlHsVarApps func_name args

tx_tys :: Module -> Module
tx_tys (Module l ms ps mw me is ds) = Module l ms ps mw me is' ds'
  where
  is' = is ++ [debug_trace_imp, text_show_fun_imp]
  ds' = everywhere (mkT tx_ty) ds

  debug_trace_imp = ImportDecl noLoc (ModuleName "Debug.Trace") True False False Nothing Nothing Nothing
  text_show_fun_imp = ImportDecl noLoc (ModuleName "Text.Show.Functions") True False False Nothing Nothing Nothing

  -- TODO: ugh, have to replicate func's type, and add relevant Show constraints
  -- to both.. (and possibly other functions (!) that call func)
  -- - maybe instead we can drop *all* type sigs?
  -- - possible problem there is that LH type will be too specific compared to inferred GHC type..
  -- - probably worth a shot though...
  -- wrapper_ty = undefined
  tx_ty :: Decl -> Decl
  tx_ty (TypeSig l xs t) = TypeSig l xs (mkShow t)
  tx_ty sig              = sig

  mkShow :: Type -> Type
  mkShow t = mkQualifiedForallTy show_ctxt t
    where
    mkQualifiedForallTy []   = id
    mkQualifiedForallTy ctxt = TyForall Nothing ctxt

    show_ctxt = map show_ct tvs
    show_ct tv = ClassA (UnQual $ name "Show") [tv]

    tvs = nub $ listify (\name -> isTyVar name) t
    isTyVar :: Type -> Bool
    isTyVar (TyVar {}) = True
    isTyVar _          = False


mkWrapperHSE :: Module -> String -> Module
mkWrapperHSE (Module l mn ps mw me is ds) func = Module l mn ps mw me is ds'
  where
  ds' = (everywhere (mkT tx_wrap) ds) ++ [wrapper]

  func_name    = name func
  wrapped_name = name $ "wrapper_" ++ func

  -- tx = tx_wrap `extT` tx_ty

  tx_wrap :: Exp -> Exp
  tx_wrap (Var v)
    | v == UnQual func_name
    = Var $ UnQual wrapped_name
  tx_wrap e
    = e

  -- TODO: args should be a list of argument names for the wrapper function.
  -- generate from the definition of the actual function
  args = case find (\fb -> func_name == fun_id fb) fun_binds of
           Just fb -> map (name . (:[])) $
                      take (fun_arity fb) ['a' ..]
           Nothing -> error ("could not find binder for: " ++ func)
  fun_binds = [ m | FunBind (m:_) <- ds ]
  fun_id (Match _ n _ _ _ _) = n
  fun_arity (Match _ _ ps _ _ _) = length ps

  -- wrapper = noLoc (ValD (FunBind (noLoc wrapped_name)
  --                                False
  --                                (MG [noLoc (Match Nothing args Nothing [grhs])] (map (const PlaceHolder) args) PlaceHolder Generated)
  --                                WpHole
  --                                PlaceHolder
  --                                []))
  wrapper = fun_bind -- L (getLoc . fun_id $ (head fun_binds)) (ValD (unLoc fun_bind))
  fun_bind = FunBind
             [Match
               noLoc
               wrapped_name
               (map pvar args)
               Nothing
               (UnGuardedRhs body)
               Nothing
             ]
  -- grhs = GRHSs [noLoc (GHRS [] body)] EmptyLocalBinds
  body = appFun traceShowName [traced, payload]
  traceShowName = qvar (ModuleName "Debug.Trace") (name "traceShow")
  traced = tuple $ (strE func) : map var args
  payload = appFun (var $ func_name) (map var args)

main :: IO ()
main = do
  fp : funcs <- getArgs
  (mod, comments) <- parseFileWithComments defaultParseMode fp >>= \case
    ParseOk x -> return x
    ParseFailed loc e -> error (show (loc, e))
  let wrap_mod = tx_tys $ foldl' mkWrapperHSE mod funcs
  putStrLn $ prettyPrint wrap_mod
  mapM_ (putStrLn . (\(Comment _ _ c) -> "{-" ++ c ++ "-}")) comments
