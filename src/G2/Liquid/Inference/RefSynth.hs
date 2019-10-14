{-# LANGUAGE OverloadedStrings #-}

module G2.Liquid.Inference.RefSynth (refSynth) where

import G2.Language.Naming
import G2.Language.Syntax as G2
import G2.Language.Typing
import G2.Liquid.Inference.FuncConstraint

import Sygus.LexSygus
import Sygus.ParseSygus
import Sygus.Print
import Sygus.Syntax as Sy
import Language.Haskell.Liquid.Types as LH
import Language.Fixpoint.Types.Refinements as LH
import qualified Language.Fixpoint.Types as LH

import Control.Exception
import Data.Coerce
import qualified Data.Map as M
import qualified Data.Text as T
import System.Directory
import System.IO
import System.IO.Temp
import qualified System.Process as P

refSynth :: SpecType -> [FuncConstraint] -> IO LH.Expr
refSynth spec fc = do
    let sygus = printSygus $ sygusCall fc

    res <- try (
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

    case res of
        Left _ -> error "refSynth: Bad call to CVC4"
        Right res' -> do
            putStrLn . T.unpack $ sygus
            let smt_st = parse . lexSygus $ stripUnsat res'
                lh_st = refToLHExpr spec smt_st

            print smt_st

            return lh_st

-------------------------------
-- Calling Sygus
-------------------------------

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

exprToTerm :: G2.Expr -> Term
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

-------------------------------
-- Converting to refinement
-------------------------------

stripUnsat :: String -> String
stripUnsat ('u':'n':'s':'a':'t':xs) = xs
stripUnsat xs = xs

refToLHExpr :: SpecType -> [Cmd] -> LH.Expr
refToLHExpr st [SmtCmd cmd] = refToLHExpr' st cmd

refToLHExpr' :: SpecType -> SmtCmd -> LH.Expr
refToLHExpr' st (DefineFun _ args _ trm) =
    let
        args' = map (\(SortedVar sym _) -> sym) args

        symbs = specTypeSymbols st
        symbsArgs = M.fromList $ zip args' symbs
    in
    termToLHExpr symbsArgs trm

termToLHExpr :: M.Map Sy.Symbol LH.Symbol -> Term -> LH.Expr
termToLHExpr m (TermIdent (ISymb v)) =
    case M.lookup v m of
        Just v' -> EVar v'
        Nothing -> error "termToLHExpr: Variable not found"
termToLHExpr m (TermCall (ISymb v) ts)
    -- EBin
    | "+" <- v
    , [t1, t2] <- ts = EBin LH.Plus (termToLHExpr m t1) (termToLHExpr m t2)
    | "-" <- v
    , [t1, t2] <- ts = EBin LH.Minus (termToLHExpr m t1) (termToLHExpr m t2)
    | "*" <- v
    , [t1, t2] <- ts = EBin LH.Times (termToLHExpr m t1) (termToLHExpr m t2)
    | "mod" <- v
    , [t1, t2] <- ts = EBin LH.Mod (termToLHExpr m t1) (termToLHExpr m t2)
    -- More EBin...
    | "and" <- v = PAnd $ map (termToLHExpr m) ts
    | "or" <- v = POr $ map (termToLHExpr m) ts
    | "not" <- v, [t1] <- ts = PNot (termToLHExpr m t1)
    -- PAtom
    | "=" <- v
    , [t1, t2] <- ts = PAtom LH.Eq (termToLHExpr m t1) (termToLHExpr m t2)
    | ">" <- v 
    , [t1, t2] <- ts = PAtom LH.Gt (termToLHExpr m t1) (termToLHExpr m t2)
     | ">=" <- v 
    , [t1, t2] <- ts = PAtom LH.Ge (termToLHExpr m t1) (termToLHExpr m t2)
    | "<" <- v 
    , [t1, t2] <- ts = PAtom LH.Lt (termToLHExpr m t1) (termToLHExpr m t2)
   | "<=" <- v 
    , [t1, t2] <- ts = PAtom LH.Le (termToLHExpr m t1) (termToLHExpr m t2)
    -- More PAtom...

specTypeSymbols :: SpecType -> [LH.Symbol]
specTypeSymbols (RFun { rt_bind = b, rt_out = out }) = b:specTypeSymbols out
specTypeSymbols (RApp { rt_reft = ref }) = [reftSymbol $ ur_reft ref]
specTypeSymbols (RVar {}) = error "RVar"
specTypeSymbols (RAllT {}) = error "RAllT"

reftSymbol :: Reft -> LH.Symbol
reftSymbol = fst . unpackReft

unpackReft :: Reft -> (LH.Symbol, LH.Expr) 
unpackReft = coerce

