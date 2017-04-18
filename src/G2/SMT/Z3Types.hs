module G2.SMT.Z3Types where

import G2.Core.Language
import G2.Core.Utils
import G2.Haskell.Prelude

import Data.List
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S

import Z3.Monad

import qualified Debug.Trace as T

type ConsFuncDecl = FuncDecl
type RecognizerFuncDecl = FuncDecl
type AccessorFuncDecl = FuncDecl

data TypeMaps = TypeMaps { types :: M.Map Name Sort
                   , consFuncs :: M.Map Name ConsFuncDecl
                   , recFuncs :: M.Map Name RecognizerFuncDecl
                   , accessorFuncs :: M.Map Name [AccessorFuncDecl] }

mkDatatypesZ3 :: TEnv -> Z3 TypeMaps
mkDatatypesZ3 tenv = mkSortsZ3 (TypeMaps {types = M.empty, consFuncs = M.empty, recFuncs = M.empty, accessorFuncs = M.empty})
                     . M.toList
                     . M.filterWithKey (\k _  -> not (k `S.member` knownTypes)) $ tenv
    where
        knownTypes = S.fromList . map fst $ prelude_t_decls

        requires :: Type -> [Name]
        requires (TyAlg n1 t1) = 
            catMaybes . map names . concat . map (\(DC (_, _, _, t')) -> t') $ t1
        requires _ = error "Must only pass TyAlg's to requires in mkDatatypesZ3"

        names :: Type -> Maybe Name
        names (TyConApp n _) = Just n 
        names _ = Nothing

        mkSortsZ3 :: TypeMaps -> [(Name, Type)] -> Z3 TypeMaps
        mkSortsZ3 tm@TypeMaps {types = d, consFuncs = c, recFuncs = r, accessorFuncs = a} ((n, t@(TyAlg n' dcs)):xs) = do
            let req = requires t

            let (s, s') = partition (\(n'', _) -> n'' `elem` req) xs
            tm' <- mkSortsZ3 tm s

            let d' = types tm'
            let c' = consFuncs tm'
            let r' = recFuncs tm'
            let a' = accessorFuncs tm'

            cons <- mapM (mkConstructorZ3 tm') dcs
            nSymb <- mkStringSymbol n
            da <- mkDatatype nSymb (map (\(_, c, _) -> c) cons)
           
            cons' <- getDatatypeSortConstructors da
            recog <- getDatatypeSortRecognizers da
            accs <- getDatatypeSortConstructorAccessors da            

            let consFuncDecls = zip (map (\(c, _, _) -> c) cons) cons'
            let recsFuncDecls = zip (map (\(c, _, _) -> c) cons) recog
            let accessorFuncDecls = zip (map (\(c, _, _) -> c) cons) accs

            let c'' = M.union c' (M.fromList $ consFuncDecls)
            let r'' = M.union r' (M.fromList $ recsFuncDecls)
            let a'' = M.union a' (M.fromList $ accessorFuncDecls)

            T.trace (show a'') mkSortsZ3 TypeMaps {types = (M.insert n da d'), consFuncs = c'', recFuncs = r'', accessorFuncs = a''} s'
        mkSortsZ3 tm [] = return tm

        getAccessors :: TypeMaps -> Sort -> [(Symbol, Sort)] -> Z3 [FuncDecl]
        getAccessors tm d ((sym, ret):xs) = do
            fd <- mkFuncDecl sym [d] ret
            acc <- getAccessors tm d xs
            return (fd:acc)
        getAccessors _ _ [] = return []

mkConstructorZ3 :: TypeMaps -> DataCon -> Z3 (Name, Constructor, [Symbol])
--we need to do something to ensure all symbols are unique... adjust
mkConstructorZ3 d (DC (n, _, tc, t)) = do
    n' <- mkStringSymbol n
    is_n <- mkStringSymbol ("is_" ++ n)
    accs <- mapM mkStringSymbol . numFresh ("acc_" ++ n) (length t) $ []
    sorts <- mapM (\_t -> if _t /= tc then return .  Just =<< sortZ3 d _t else return  Nothing) t

    cons <- mkConstructor n' is_n . map (\(a, s) -> (a, s, 0)) . zip accs $ sorts

    return (n, cons, accs)

sortFuncZ3 :: TypeMaps -> Type -> Z3 [Sort]
sortFuncZ3 d (TyFun t1 t2) = do
    t1' <- sortFuncZ3 d t1
    t2' <- sortFuncZ3 d t2
    return (t1' ++ t2')
sortFuncZ3 d t = do
    t' <- sortZ3 d t
    return [t']

sortZ3 :: TypeMaps -> Type -> Z3 Sort
sortZ3 _ TyRawInt = mkIntSort
sortZ3 _ (TyConApp "Int" _) = mkIntSort
sortZ3 _ TyRawFloat = mkRealSort
sortZ3 _ (TyConApp "Float" _) = mkRealSort
sortZ3 _ TyRawDouble = mkRealSort
sortZ3 _ (TyConApp "Double" _) = mkRealSort
sortZ3 _ (TyConApp "Bool" _) = mkBoolSort
sortZ3 tm t@(TyConApp n _) =
    let
        r = M.lookup n . types $ tm
    in
    case r of (Just r') -> return r'
              Nothing -> error ("Unknown sort in sortZ3 " ++ show t)
sortZ3 _ t = error ("Unknown sort in sortZ3 " ++ show t)