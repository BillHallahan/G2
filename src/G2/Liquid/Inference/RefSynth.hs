{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.RefSynth (refSynth) where

import G2.Language.Naming
import G2.Language.Syntax as G2
import G2.Language.Typing
import G2.Liquid.Inference.FuncConstraint
import Sygus.Print
import Sygus.Syntax
import Language.Haskell.Liquid.Types

import Control.Exception
import qualified Data.Text as T
import System.Directory
import System.IO
import System.IO.Temp
import qualified System.Process as P

refSynth :: [FuncConstraint] -> IO ()
refSynth fc = do
    let sygus = printSygus $ sygusCall fc

    out <- try (
        withSystemTempFile ("cvc4_input.sy")
        (\fp h -> do
            hPutStr h (T.unpack sygus)
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            toCommandOSX <- findExecutable "gtimeout" 
            let toCommand = case toCommandOSX of
                    Just c -> c          -- Mac
                    Nothing -> "timeout" -- Linux

            P.readProcess toCommand ["10", "cvc4", fp, "--lang=sygus2"] "")
        ) :: IO (Either SomeException String)

    case out of
        Left _ -> error "refSynth: Bad call to CVC4"
        Right out' -> do
            putStrLn . T.unpack $ sygus
            putStrLn out'
            return ()

sygusCall :: [FuncConstraint] -> [Cmd]
sygusCall fcs@(fc:_) =
    let
        ts = map typeOf (arguments $ constraint fc) ++ [typeOf (returns $ constraint fc)]

        varN = map (\i -> "x" ++ show i) ([0..] :: [Integer])
        sortVars = map (uncurry SortedVar) . zip varN $ map typeToSorts ts
    in
    [ SmtCmd (SetLogic "ALL")
    , SynthFun "refinement" sortVars boolSort (Just grammar) ]
    ++
    map constraints fcs
    ++
    [ CheckSynth ]
sygusCall _ = error "sygusCall: empty list"

grammar :: GrammarDef
grammar =
    GrammarDef
        [ SortedVar "B" boolSort
        , SortedVar "I" intSort ]
        [ GroupedRuleList "B" boolSort 
            [ GVariable boolSort
            , GBfTerm $ BfIdentifierBfs (ISymb "=") [intBf, intBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "<") [intBf, intBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "=>") [boolBf, boolBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "and") [boolBf, boolBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "or") [boolBf, boolBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "not") [boolBf]
            ]
        , GroupedRuleList "I" intSort 
            [ GVariable intSort
            , GBfTerm $ BfIdentifierBfs (ISymb "+") [intBf, intBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "-") [intBf, intBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "*") [intBf, intBf]
            , GBfTerm $ BfIdentifierBfs (ISymb "mod") [intBf, intBf]
            ]
        ]

constraints :: FuncConstraint -> Cmd
constraints (Pos fc) =
    Constraint $ TermCall (ISymb "=") [funcCallTerm fc, TermLit (LitBool True)]
constraints (Neg fc) =
    Constraint $ TermCall (ISymb "=") [funcCallTerm fc, TermLit (LitBool False)]

funcCallTerm :: FuncCall -> Term
funcCallTerm (FuncCall { arguments = args, returns = r}) =
    TermCall (ISymb "refinement") (map exprToTerm args ++ [exprToTerm r])

exprToTerm :: Expr -> Term
exprToTerm (App _ (Lit l)) = litToTerm l
exprToTerm _ = error "exprToTerm: Unhandled Expr"

litToTerm :: G2.Lit -> Term
litToTerm (LitInt i) = TermLit (LitNum i)
litToTerm _ = error "litToTerm: Unhandled Lit"

typeToSorts :: Type -> Sort
typeToSorts (TyCon n@(Name n' _ _ _) _) 
    | n' == "Int" = intSort
    | n' == "Bool" = boolSort
    | otherwise = IdentSort . ISymb $ nameToStr n

intBf :: BfTerm
intBf = BfIdentifier (ISymb "I")

boolBf :: BfTerm
boolBf = BfIdentifier (ISymb "B")

intSort :: Sort
intSort = IdentSort (ISymb "Int")

boolSort :: Sort
boolSort = IdentSort (ISymb "Bool")