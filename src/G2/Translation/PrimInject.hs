{-# LANGUAGE CPP, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Primitive inejction into the environment
module G2.Translation.PrimInject
    ( primInject
    , dataInject
    , addPrimsToBase
    , mergeProgs
    , mergeProgTys
    ) where

import G2.Language.AST
import G2.Language.Expr
import G2.Language.Naming
import G2.Language.Support
import G2.Language.Syntax
import G2.Language.Typing

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Text as T

primInject :: ASTContainer p Type => p -> p
primInject = modifyASTs primInjectT

primInjectT :: Type -> Type
primInjectT (TyCon (Name "TYPE" (Just "GHC.Prim") _ _) _) = TYPE
primInjectT (TyCon (Name "Int#" _ _ _) _) = TyLitInt
primInjectT (TyCon (Name "Word#" _ _ _) _) = TyLitWord
primInjectT (TyCon (Name "Float#" _ _ _) _) = TyLitFloat
primInjectT (TyCon (Name "Double#" _ _ _) _) = TyLitDouble
primInjectT (TyCon (Name "Char#" _ _ _) _) = TyLitChar
primInjectT t = t

dataInject :: (ASTContainer t Expr) => t -> HM.HashMap Name AlgDataTy -> t
dataInject prog progTy = 
    let
        dcNames = concatMap (map conName . dataCon) $ progTy
    in
    modifyASTs (dataInject' dcNames) prog

-- TODO: Polymorphic types?
dataInject' :: [(Name, [Type], [Id], [Id])] -> Expr -> Expr
dataInject' ns v@(Var (Id (Name n m _ _) t)) = 
    case find (\(Name n' m' _ _, _, _, _) -> n == n' && m == m') ns of
        Just (n', _, u, e) -> Data (DataCon n' t u e)
        Nothing -> v
dataInject' _ e = e

conName :: DataCon -> (Name, [Type], [Id], [Id])
conName (DataCon n t u e) = (n, anonArgumentTypes t, u, e)

primDefs :: HM.HashMap Name AlgDataTy -> [(T.Text, Expr)]
primDefs pt = case (boolName pt, charName pt, listName pt, unitName pt) of
                (Just b, Just c, Just l, Just unit) -> primDefs' b c l unit
                _ -> error "primDefs: Required types not found"

primDefs' :: Name -> Name -> Name -> Name -> [(T.Text, Expr)]
primDefs' b c l unit =
              [ ("$==#", Prim Eq $ tyIntIntBool b)
              , ("$/=#", Prim Neq $ tyIntIntBool b)
              , ("+#", Prim Plus tyIntIntInt)
              , ("*#", Prim Mult tyIntIntInt)
              , ("-#", Prim Minus tyIntIntInt)
              , ("negateInt#", Prim Negate tyIntInt)
              , ("$<=#", Prim Le $ tyIntIntBool b)
              , ("$<#", Prim Lt $ tyIntIntBool b)
              , ("$>#", Prim Gt $ tyIntIntBool b)
              , ("$>=#", Prim Ge $ tyIntIntBool b)
              , ("divInt#", Prim Quot tyIntIntInt)
              , ("modInt#", Prim Mod tyIntIntInt)
              , ("quotInt#", Prim Quot tyIntIntInt)
              , ("remInt#", Prim Rem tyIntIntInt)

              , ("$==##", Prim FpEq $ tyDoubleDoubleBool b)
              , ("$/=##", Prim FpNeq $ tyDoubleDoubleBool b)
              , ("+##", Prim FpAdd tyDoubleDoubleDouble)
              , ("*##", Prim FpMul tyDoubleDoubleDouble)
              , ("-##", Prim FpSub tyDoubleDoubleDouble)
              , ("negateDouble#", Prim FpNeg tyDoubleDouble)
              , ("sqrtDouble#", Prim FpSqrt tyDoubleDouble)
              , ("truncZeroDouble#", Prim TruncZero tyDoubleInteger)
              , ("decPartDouble#", Prim DecimalPart tyDoubleDouble)
              , ("/##", Prim FpDiv tyDoubleDoubleDouble)
              , ("$<=##", Prim FpLeq $ tyDoubleDoubleBool b)
              , ("$<##", Prim FpLt $ tyDoubleDoubleBool b)
              , ("$>##", Prim FpGt $ tyDoubleDoubleBool b)
              , ("$>=##", Prim FpGeq $ tyDoubleDoubleBool b)

              , ("decodeDouble#", Prim DecodeFloat tyDoubleInteger)
              , ("encodeDoubleInteger#", Prim EncodeFloat tyIntIntDouble)
              , ("isDoubleNegativeZero#", Prim FpIsNegativeZero $ tyDoubleBool b)
              , ("isDoubleDenormalized#", Prim IsDenormalized $ tyDoubleBool b)
              , ("isDoubleNaN#", Prim IsNaN $ tyDoubleBool b)
              , ("isDoubleInfinite#", Prim IsInfinite $ tyDoubleBool b)

              , ("plusFloat#", Prim FpAdd tyFloatFloatFloat)
              , ("timesFloat#", Prim FpMul tyFloatFloatFloat)
              , ("minusFloat#", Prim FpSub tyFloatFloatFloat)
              , ("negateFloat#", Prim FpNeg tyFloatFloat)
              , ("sqrtFloat#", Prim FpSqrt tyFloatFloat)
              , ("truncZeroFloat#", Prim TruncZero tyFloatInteger)
              , ("decPartFloat#", Prim DecimalPart tyFloatFloat)
              , ("divideFloat#", Prim FpDiv tyFloatFloatFloat)
              , ("smtEqFloat#", Prim FpEq $ tyFloatFloatBool b)
              , ("smtNeFloat#", Prim FpNeq $ tyFloatFloatBool b)
              , ("smtLeFloat#", Prim FpLeq $ tyFloatFloatBool b)
              , ("smtLtFloat#", Prim FpLt $ tyFloatFloatBool b)
              , ("smtGtFloat#", Prim FpGt $ tyFloatFloatBool b)
              , ("smtGeFloat#", Prim FpGeq $ tyFloatFloatBool b)

              , ("decodeFloat#", Prim DecodeFloat tyFloatInteger)
              , ("encodeFloatInteger#", Prim EncodeFloat tyIntIntFloat)
              , ("isFloatNegativeZero#", Prim FpIsNegativeZero $ tyFloatBool b)
              , ("isFloatDenormalized#", Prim IsDenormalized $ tyFloatBool b)
              , ("isFloatNaN#", Prim IsNaN $ tyFloatBool b)
              , ("isFloatInfinite#", Prim IsInfinite $ tyFloatBool b)

              , ("quotInteger#", Prim Quot tyIntIntInt)
              , ("remInteger#", Prim Rem tyIntIntInt)

              , ("chr#", Prim Chr $ tyIntChar b )
              , ("ord#", Prim OrdChar $ tyCharInt b )
              , ("smtEqChar#", Prim Eq $ tyCharCharBool b )
              , ("smtNeChar#", Prim Neq $ tyCharCharBool b )
              , ("smtEqChar#", Prim Eq $ tyCharCharBool b )
              , ("gtChar#", Prim StrGt $ tyCharCharBool b )
              , ("geChar#", Prim StrGe $ tyCharCharBool b )
              , ("ltChar#", Prim StrLt $ tyCharCharBool b )
              , ("leChar#", Prim StrLe $ tyCharCharBool b )
              , ("wgencat#", Prim WGenCat $ tyIntInt )

              , ("float2Int#", Prim ToInt (TyFun TyLitFloat TyLitInt))
              , ("int2Float#", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("fromIntToFloat", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("double2Int#", Prim ToInt (TyFun TyLitDouble TyLitInt))
              , ("int2Double#", Prim IntToDouble (TyFun TyLitInt TyLitDouble))
              , ("float2Double#", Prim FloatToDouble (TyFun TyLitFloat TyLitDouble))
              , ("double2Float#", Prim DoubleToFloat (TyFun TyLitDouble TyLitFloat))
              , ("rationalToFloat#", Prim RationalToFloat (TyFun TyLitInt $ TyFun TyLitInt TyLitFloat))
              , ("rationalToDouble#", Prim RationalToDouble (TyFun TyLitInt $ TyFun TyLitInt TyLitDouble))
              , ("fromIntToDouble", Prim IntToDouble (TyFun TyLitInt TyLitDouble))

              , ("integerToWord#", Lam TermL (x TyLitWord) (Var (x TyLitWord)))
              , ("plusWord#", Prim Plus tyWordWordWord)
              , ("minusWord#", Prim Minus tyWordWordWord)
              , ("timesWord#", Prim Mult tyWordWordWord)
              , ("eqWord#", Prim Eq $ tyWordWordBool b)
              , ("neWord#", Prim Neq $ tyWordWordBool b)
              , ("gtWord#", Prim Gt $ tyWordWordBool b)
              , ("geWord#", Prim Ge $ tyWordWordBool b)
              , ("ltWord#", Prim Lt $ tyWordWordBool b)
              , ("leWord#", Prim Le $ tyWordWordBool b)

              , ("dataToTag##", Prim DataToTag (TyForAll a (TyFun (TyVar a) TyLitInt)))
              , ("tagToEnum#", 
                    Lam TypeL a
                        . Lam TermL (y tyvarA)
                            $ Case (Var (y tyvarA)) (binder tyvarA) tyvarA 
                            [ Alt Default
                                   $ App
                                        (App
                                            (Prim TagToEnum (TyForAll a (TyFun TyLitInt tyvarA)))
                                            (Var a))
                                        (Var $ y tyvarA)

                            ])
              
              , ("stdin", Prim (Handle stdinName) TyUnknown)
              , ("stdout", Prim (Handle stdoutName) TyUnknown)
              , ("stderr", Prim (Handle stderrName) TyUnknown)
              , ("g2GetPos'", Prim HandleGetPos (TyFun TyUnknown strTy))
              , ("g2SetPos'", Prim HandleSetPos (TyFun strTy (TyFun TyUnknown (TyCon unit TYPE))))
              , ("g2PutChar'", Prim HandlePutChar (TyFun (TyCon c TYPE) (TyFun TyUnknown (TyCon unit TYPE))))

              , ("strLen#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) $ App (Prim StrLen (TyFun seqTyX TyLitInt)) (Var $ y seqTyX))
              , ("strAppend#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z seqTyX)
                                  $ App 
                                      (App 
                                          (Prim StrAppend ((TyFun seqTyX) $ TyFun seqTyX seqTyX))
                                          (Var $ y seqTyX))
                                      (Var $ z seqTyX))
              , ("strAt#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z TyLitInt)
                            $ App 
                                (App 
                                    (Prim StrAt ((TyFun seqTyX) $ TyFun TyLitInt seqTyX))
                                    (Var $ y seqTyX))
                                (Var $ z TyLitInt))
              , ("strSubstr#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z TyLitInt) . Lam TermL ((dummyId "q") TyLitInt)
                            $ App
                                (App
                                    (App
                                        (Prim StrSubstr (TyFun seqTyX (TyFun TyLitInt (TyFun TyLitInt seqTyX))))
                                        (Var $ y seqTyX))
                                    (Var $ z TyLitInt))
                                (Var $ (dummyId "q") TyLitInt))
              , ("strEq#", strStrBool Eq)
              , ("strLt#", strStrBool StrLt)
              , ("strLe#", strStrBool StrLe)
              , ("strGt#", strStrBool StrGt)
              , ("strGe#", strStrBool StrGe)
              , ("strIndexOf#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z seqTyX) . Lam TermL ((dummyId "q") TyLitInt)
                            $ App
                                (App
                                    (App
                                        (Prim StrIndexOf (TyFun seqTyX (TyFun seqTyX (TyFun TyLitInt TyLitInt))))
                                        (Var $ y seqTyX))
                                    (Var $ z seqTyX))
                                (Var $ (dummyId "q") TyLitInt))
              , ("strReplace#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z seqTyX) . Lam TermL ((dummyId "q") seqTyX)
                            $ App
                                (App
                                    (App
                                        (Prim StrReplace (TyFun seqTyX (TyFun seqTyX (TyFun seqTyX seqTyX))))
                                        (Var $ y seqTyX))
                                    (Var $ z seqTyX))
                                (Var $ (dummyId "q") seqTyX))
              , ("strPrefixOf#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z seqTyX)
                            $ App
                                (App
                                    (Prim StrPrefixOf (TyFun seqTyX (TyFun seqTyX (TyCon b TYPE))))
                                    (Var $ y seqTyX)
                                )
                                (Var $ z seqTyX))
              , ("strSuffixOf#", Lam TypeL (x TYPE) . Lam TermL (y seqTyX) . Lam TermL (z seqTyX)
                            $ App
                                (App
                                    (Prim StrSuffixOf (TyFun seqTyX (TyFun seqTyX (TyCon b TYPE))))
                                    (Var $ y seqTyX)
                                )
                                (Var $ z seqTyX))
              , ("intToString#", Prim IntToString (TyFun TyLitInt strTy))

              , ("newMutVar##", Prim NewMutVar (TyForAll a (TyForAll d (TyFun tyvarA (TyFun TyUnknown TyUnknown)))))
              , ("readMutVar##", Prim ReadMutVar (TyForAll d (TyForAll a (TyFun TyUnknown (TyFun TyUnknown tyvarA)))))
              , ("writeMutVar##", Prim WriteMutVar (TyForAll d (TyForAll a (TyFun tyvarA (TyFun TyUnknown TyUnknown)))))

              , ("absentErr", Prim Error TyBottom)
              , ("error", Prim Error TyBottom)
              , ("errorWithoutStackTrace", Prim Error TyBottom)
              , ("divZeroError", Prim Error TyBottom)
              , ("overflowError", Prim Error TyBottom)
              , ("patError", Prim Error TyBottom)
              , ("succError", Prim Error TyBottom)
              , ("toEnumError", Prim Error TyBottom)
              , ("ratioZeroDenominatorError", Prim Error TyBottom)
              , ("undefined", Prim Error TyBottom)

              , ("ite", Lam TypeL a (iteExpr (TyVar a)))
              , ("iteInt#", iteExpr TyLitInt)
              , ("iteChar#", iteExpr TyLitChar)

              , ("&&#", Prim And . TyFun (TyCon b TYPE) $ TyFun (TyCon b TYPE) (TyCon b TYPE))
              , ("||#", Prim Or . TyFun (TyCon b TYPE) $ TyFun (TyCon b TYPE) (TyCon b TYPE))
              , ("==>", Prim Implies . TyFun (TyCon b TYPE) $ TyFun (TyCon b TYPE) (TyCon b TYPE))
              
              , ("forAllBoundInt#", Prim ForAllBoundPr (mkTyFun [ TyLitInt
                                                                , TyLitInt
                                                                , TyFun TyLitInt (TyCon b TYPE)
                                                                , TyCon b TYPE]))

              , ("isSMTRep#", Prim IsSMTRep (TyForAll a (TyFun (TyVar a) (TyCon b TYPE))))
              , ("evalsToSMTRep#", Prim EvalsToSMTRep (TyForAll a (TyFun (TyVar a) (TyCon b TYPE))))
              , ("typeIndex#", Prim (TypeIndex (TyH { tyh_strings = False, tyh_prim_lists = False })) (TyForAll a (TyFun (TyVar a) TyLitInt))) ]
              where
                    seqTy v = (TyApp (TyCon l (TyFun TYPE TYPE)) v)
                    seqTyX = seqTy (TyVar (x TYPE))
                    strTy = seqTy (TyCon c TYPE)

                    strStrBool op = 
                        Lam TypeL (x TYPE) . Lam TermL (y strTy) . Lam TermL (z strTy)
                            $ App 
                                (App
                                    (Prim op ((TyFun strTy) $ TyFun strTy (TyCon b TYPE)))
                                    (Var $ y strTy))
                                (Var $ z strTy)
                    
                    iteExpr t =
                         Lam TermL (z $ TyCon b TYPE) . Lam TermL (x t) . Lam TermL (y t)
                            $ Case (Var (z $ TyCon b TYPE))
                                   (binder $ TyCon b TYPE)
                                   t
                                   [Alt Default $
                                        mkApp [ Prim Ite (TyFun (TyCon b TYPE) (TyFun t (TyFun t t)))
                                                , Var . z $ TyCon b TYPE
                                                , Var $ x t
                                                , Var $ y t]]
a :: Id
a = Id (Name "a" Nothing 0 Nothing) TYPE

tyvarA :: Type
tyvarA = TyVar a

d :: Id
d = Id (Name "d" Nothing 0 Nothing) TYPE

x :: Type -> Id
x = Id (Name "x" Nothing 0 Nothing)

y :: Type -> Id
y = Id (Name "y" Nothing 0 Nothing)

z :: Type -> Id
z = Id (Name "z" Nothing 0 Nothing)

dummyId :: T.Text -> Type -> Id
dummyId name = Id (Name name Nothing 0 Nothing) 

binder :: Type -> Id
binder = Id (Name "b" Nothing 0 Nothing)

tyIntInt :: Type
tyIntInt = TyFun TyLitInt TyLitInt

tyIntIntBool :: Name -> Type
tyIntIntBool n = TyFun TyLitInt $ TyFun TyLitInt (TyCon n TYPE)

tyIntIntInt :: Type
tyIntIntInt = TyFun TyLitInt $ TyFun TyLitInt TyLitInt

tyWordWordBool :: Name -> Type
tyWordWordBool n = TyFun TyLitWord $ TyFun TyLitWord (TyCon n TYPE)

tyWordWordWord :: Type
tyWordWordWord = TyFun TyLitWord $ TyFun TyLitWord TyLitWord

tyDoubleDouble :: Type
tyDoubleDouble = TyFun TyLitDouble TyLitDouble

tyDoubleInteger :: Type
tyDoubleInteger = TyFun TyLitDouble TyLitInt

tyIntIntDouble :: Type
tyIntIntDouble = TyFun TyLitInt (TyFun TyLitInt TyLitDouble)

tyDoubleBool :: Name -> Type
tyDoubleBool n = TyFun TyLitDouble (TyCon n TYPE)

tyDoubleDoubleBool :: Name -> Type
tyDoubleDoubleBool n = TyFun TyLitDouble $ TyFun TyLitDouble (TyCon n TYPE)

tyDoubleDoubleDouble :: Type
tyDoubleDoubleDouble = TyFun TyLitDouble $ TyFun TyLitDouble TyLitDouble

tyFloatFloat :: Type
tyFloatFloat = TyFun TyLitFloat TyLitFloat

tyFloatInteger :: Type
tyFloatInteger = TyFun TyLitFloat TyLitInt

tyIntIntFloat :: Type
tyIntIntFloat = TyFun TyLitInt (TyFun TyLitInt TyLitFloat)

tyFloatBool :: Name -> Type
tyFloatBool n = TyFun TyLitFloat (TyCon n TYPE)

tyFloatFloatBool :: Name -> Type
tyFloatFloatBool n = TyFun TyLitFloat $ TyFun TyLitFloat (TyCon n TYPE)

tyFloatFloatFloat :: Type
tyFloatFloatFloat = TyFun TyLitFloat $ TyFun TyLitFloat TyLitFloat

tyIntCharBool :: Name -> Type
tyIntCharBool n = TyFun TyLitInt $ TyFun TyLitChar (TyCon n TYPE)

tyIntChar :: Name -> Type
tyIntChar n = TyFun TyLitInt TyLitChar

tyCharInt :: Name -> Type
tyCharInt n = TyFun TyLitChar TyLitInt

tyCharIntBool :: Name -> Type
tyCharIntBool n = TyFun TyLitChar $ TyFun TyLitInt (TyCon n TYPE)

tyCharCharBool :: Name -> Type
tyCharCharBool n = TyFun TyLitChar $ TyFun TyLitChar (TyCon n TYPE)

boolName :: HM.HashMap Name AlgDataTy -> Maybe Name
boolName = find ((==) "Bool" . nameOcc) . HM.keys

charName :: HM.HashMap Name AlgDataTy -> Maybe Name
charName = find ((==) "Char" . nameOcc) . HM.keys

listName :: HM.HashMap Name AlgDataTy -> Maybe Name
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
listName = find ((==) "List" . nameOcc) . HM.keys
#else
listName = find ((==) "[]" . nameOcc) . HM.keys
#endif

unitName :: HM.HashMap Name AlgDataTy -> Maybe Name
#if MIN_VERSION_GLASGOW_HASKELL(9,8,0,0)
unitName = find ((==) "Unit" . nameOcc) . HM.keys
#else
unitName = find ((==) "()" . nameOcc) . HM.keys
#endif

replaceFromPD :: HM.HashMap Name AlgDataTy -> Name -> Expr -> Expr
replaceFromPD pt n e =
    let
        e' = fmap snd $ find ((==) (nameOcc n) . fst) (primDefs pt)
    in
    maybe e id e'

addPrimsToBase :: HM.HashMap Name AlgDataTy -> HM.HashMap Name Expr -> HM.HashMap Name Expr
addPrimsToBase pt prims = HM.mapWithKey (replaceFromPD pt) prims

mergeProgs :: HM.HashMap Name Expr -> HM.HashMap Name Expr -> HM.HashMap Name Expr
mergeProgs prog prims = prog `HM.union` prims

-- The prog is used to change the names of types in the prog' and primTys
mergeProgTys :: [(Name, AlgDataTy)] -> [(Name, AlgDataTy)] -> [(Name, AlgDataTy)]
mergeProgTys progTys primTys =
    progTys ++ primTys  
