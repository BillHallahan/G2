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
import G2.Language.Naming
import G2.Language.Syntax
import G2.Language.Typing
import G2.Language.TypeEnv

import qualified Data.HashMap.Lazy as HM
import Data.List
import qualified Data.Text as T

primInject :: ASTContainer p Type => p -> p
primInject = modifyASTs primInjectT

primInjectT :: Type -> Type
primInjectT (TyCon (Name "TYPE" (Just "GHC.Prim") _ _) _) = TYPE
primInjectT (TyCon (Name "Int#" _ _ _) _) = TyLitInt
primInjectT (TyCon (Name "Word#" _ _ _) _) = TyLitInt
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
dataInject' :: [(Name, [Type])] -> Expr -> Expr
dataInject' ns v@(Var (Id (Name n m _ _) t)) = 
    case find (\(Name n' m' _ _, _) -> n == n' && m == m') ns of
        Just (n', _) -> Data (DataCon n' t)
        Nothing -> v
dataInject' _ e = e

conName :: DataCon -> (Name, [Type])
conName (DataCon n t) = (n, anonArgumentTypes $ t)

primDefs :: HM.HashMap Name AlgDataTy -> [(T.Text, Expr)]
primDefs pt = case (boolName pt, charName pt, listName pt) of
                (Just b, Just c, Just l) -> primDefs' b c l
                _ -> error "primDefs: Required types not found"

primDefs' :: Name -> Name -> Name -> [(T.Text, Expr)]
primDefs' b c l =
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

              , ("$==##", Prim Eq $ tyDoubleDoubleBool b)
              , ("$/=##", Prim Neq $ tyDoubleDoubleBool b)
              , ("+##", Prim Plus tyDoubleDoubleDouble)
              , ("*##", Prim Mult tyDoubleDoubleDouble)
              , ("-##", Prim Minus tyDoubleDoubleDouble)
              , ("negateDouble#", Prim Negate tyDoubleDouble)
              , ("sqrtDouble#", Prim SqRt tyDoubleDoubleDouble)
              , ("/##", Prim Div tyDoubleDoubleDouble)
              , ("$<=##", Prim Le $ tyDoubleDoubleBool b)
              , ("$<##", Prim Lt $ tyDoubleDoubleBool b)
              , ("$>##", Prim Gt $ tyDoubleDoubleBool b)
              , ("$>=##", Prim Ge $ tyDoubleDoubleBool b)

              , ("plusFloat#", Prim Plus tyFloatFloatFloat)
              , ("timesFloat#", Prim Mult tyFloatFloatFloat)
              , ("minusFloat#", Prim Minus tyFloatFloatFloat)
              , ("negateFloat#", Prim Negate tyFloatFloat)
              , ("sqrtFloat#", Prim SqRt tyFloatFloatFloat)
              , ("divideFloat#", Prim Div tyFloatFloatFloat)
              , ("smtEqFloat#", Prim Eq $ tyFloatFloatBool b)
              , ("smtNeFloat#", Prim Neq $ tyFloatFloatBool b)
              , ("smtLeFloat#", Prim Le $ tyFloatFloatBool b)
              , ("smtLtFloat#", Prim Lt $ tyFloatFloatBool b)
              , ("smtGtFloat#", Prim Gt $ tyFloatFloatBool b)
              , ("smtGeFloat#", Prim Ge $ tyFloatFloatBool b)

              , ("quotInteger#", Prim Quot tyIntIntInt)
              , ("remInteger#", Prim Rem tyIntIntInt)

              , ("chr#", Prim Chr $ tyIntCharBool b )
              , ("ord#", Prim OrdChar $ tyCharIntBool b )
              , ("smtEqChar#", Prim Eq $ tyCharCharBool b )
              , ("smtNeChar#", Prim Neq $ tyCharCharBool b )
              , ("smtEqChar#", Prim Eq $ tyCharCharBool b )
              , ("gtChar#", Prim Gt $ tyCharCharBool b )
              , ("geChar#", Prim Ge $ tyCharCharBool b )
              , ("ltChar#", Prim Lt $ tyCharCharBool b )
              , ("leChar#", Prim Le $ tyCharCharBool b )
              , ("wgencat#", Prim WGenCat $ tyIntInt )

              , ("float2Int#", Prim ToInt (TyFun TyLitFloat TyLitInt))
              , ("int2Float#", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("fromIntToFloat", Prim IntToFloat (TyFun TyLitInt TyLitFloat))
              , ("double2Int#", Prim ToInt (TyFun TyLitDouble TyLitInt))
              , ("int2Double#", Prim IntToDouble (TyFun TyLitInt TyLitDouble))
              , ("rationalToDouble#", Prim RationalToDouble (TyFun TyLitInt $ TyFun TyLitInt TyLitDouble))
              , ("fromIntToDouble", Prim IntToDouble (TyFun TyLitInt TyLitDouble))

              -- TODO: G2 doesn't currently draw a distinction between Integers and Words
              , ("integerToWord#", Lam TermL (x TyLitInt) (Var (x TyLitInt)))
              , ("plusWord#", Prim Plus tyIntIntInt)
              , ("minusWord#", Prim Minus tyIntIntInt)
              , ("timesWord#", Prim Mult tyIntIntInt)
              , ("eqWord#", Prim Eq $ tyIntIntBool b)
              , ("neWord#", Prim Neq $ tyIntIntBool b)
              , ("gtWord#", Prim Gt $ tyIntIntBool b)
              , ("geWord#", Prim Ge $ tyIntIntBool b)
              , ("ltWord#", Prim Lt $ tyIntIntBool b)
              , ("leWord#", Prim Le $ tyIntIntBool b)

              -- Hack to convert GHC Char to G2 Chars in base
              , ("char2char", Lam TermL (x $ TyCon c TYPE) (Var . x $ TyCon c TYPE))

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

              , ("intToString#", Prim IntToString (TyFun TyLitInt (TyApp (TyCon l (TyFun TYPE TYPE)) (TyCon c TYPE))))

              , ("absentErr", Prim Error TyBottom)
              , ("error", Prim Error TyBottom)
              , ("errorWithoutStackTrace", Prim Error TyBottom)
              , ("divZeroError", Prim Error TyBottom)
              , ("overflowError", Prim Error TyBottom)
              , ("patError", Prim Error TyBottom)
              , ("succError", Prim Error TyBottom)
              , ("toEnumError", Prim Error TyBottom)
              , ("ratioZeroDenominatorError", Prim Error TyBottom)
              , ("undefined", Prim Error TyBottom) ]

a :: Id
a = Id (Name "a" Nothing 0 Nothing) TYPE

tyvarA :: Type
tyvarA = TyVar a

x :: Type -> Id
x = Id (Name "x" Nothing 0 Nothing)

y :: Type -> Id
y = Id (Name "y" Nothing 0 Nothing)

binder :: Type -> Id
binder = Id (Name "b" Nothing 0 Nothing)

tyIntInt :: Type
tyIntInt = TyFun TyLitInt TyLitInt

tyIntIntBool :: Name -> Type
tyIntIntBool n = TyFun TyLitInt $ TyFun TyLitInt (TyCon n TYPE)

tyIntIntInt :: Type
tyIntIntInt = TyFun TyLitInt $ TyFun TyLitInt TyLitInt

tyDoubleDouble :: Type
tyDoubleDouble = TyFun TyLitDouble TyLitDouble

tyDoubleDoubleBool :: Name -> Type
tyDoubleDoubleBool n = TyFun TyLitDouble $ TyFun TyLitDouble (TyCon n TYPE)

tyDoubleDoubleDouble :: Type
tyDoubleDoubleDouble = TyFun TyLitDouble $ TyFun TyLitDouble TyLitDouble

tyFloatFloat :: Type
tyFloatFloat = TyFun TyLitFloat TyLitFloat

tyFloatFloatBool :: Name -> Type
tyFloatFloatBool n = TyFun TyLitFloat $ TyFun TyLitFloat (TyCon n TYPE)

tyFloatFloatFloat :: Type
tyFloatFloatFloat = TyFun TyLitFloat $ TyFun TyLitFloat TyLitFloat

tyIntCharBool :: Name -> Type
tyIntCharBool n = TyFun TyLitInt $ TyFun TyLitChar (TyCon n TYPE)

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
