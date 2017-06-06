module G2.Internals.SMT.Z3Types where

import G2.Internals.Core.Language
import G2.Internals.Core.Utils
import G2.Internals.Translation.Prelude

import Data.List
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Char as C
import Data.Maybe
import qualified Data.Set as S

import Z3.Monad

type TypeName = Name
type ConsFuncDecl = FuncDecl
type RecognizerFuncDecl = FuncDecl
type AccessorFuncDecl = FuncDecl

data TypeMaps = TypeMaps { types :: M.Map TypeName Sort
                   , consNamesFuncs :: M.Map Name (TypeName, ConsFuncDecl)
                   , recNamesFuncs :: M.Map Name (TypeName, RecognizerFuncDecl)
                   , accessorNamesFuncs :: M.Map Name (TypeName, [AccessorFuncDecl]) }


consFuncs :: TypeMaps -> TypeName -> Maybe ConsFuncDecl
consFuncs t n = return . snd =<< M.lookup n (consNamesFuncs t)


recFuncs :: TypeMaps -> TypeName -> Maybe RecognizerFuncDecl
recFuncs t n = return . snd =<< M.lookup n (recNamesFuncs t)

accessorFuncs :: TypeMaps -> TypeName -> Maybe [AccessorFuncDecl]
accessorFuncs t n = return . snd =<< M.lookup n (accessorNamesFuncs t)

--This needs to be adjusted to support mutually recursive datatypes
mkDatatypesZ3 :: TEnv -> Z3 TypeMaps
mkDatatypesZ3 tenv = mkSortsZ3 (TypeMaps {types = M.empty, consNamesFuncs = M.empty, recNamesFuncs = M.empty, accessorNamesFuncs = M.empty})
                     . M.toList
                     . M.filterWithKey (\k _  -> not (k `S.member` knownTypes)) $ tenv
    where
        knownTypes = S.fromList . map fst $ prelude_t_decls

        requires :: Type -> [Name]
        requires (TyAlg n1 t1) = 
            catMaybes . map names . concat . map (\(DataCon _ _ _ t') -> t') $ t1
        requires _ = error "Must only pass TyAlg's to requires in mkDatatypesZ3"

        names :: Type -> Maybe Name
        names (TyConApp n _) = Just n 
        names _ = Nothing

        mkSortsZ3 :: TypeMaps -> [(Name, Type)] -> Z3 TypeMaps
        mkSortsZ3 tm@TypeMaps {types = d, consNamesFuncs = c, recNamesFuncs = r, accessorNamesFuncs = a} ((n, t@(TyAlg n' dcs)):xs) = do
            let req = requires t

            let (s, s') = partition (\(n'', _) -> n'' `elem` req) xs
            tm' <- mkSortsZ3 tm s

            let d' = types tm'
            let c' = consNamesFuncs tm'
            let r' = recNamesFuncs tm'
            let a' = accessorNamesFuncs tm'

            cons <- mapM (mkConstructorZ3 tm') dcs
            nSymb <- mkStringSymbol n
            da <- mkDatatype nSymb (map (\(_, c, _) -> c) cons)
           
            cons' <- getDatatypeSortConstructors da
            recog <- getDatatypeSortRecognizers da
            accs <- getDatatypeSortConstructorAccessors da            

            let consFuncDecls = zip (map (\(c, _, _) -> c) cons) (map (\c -> (n, c)) cons')
            let recsFuncDecls = zip (map (\(c, _, _) -> c) cons) (map (\r -> (n, r)) recog)
            let accessorFuncDecls = zip (map (\(c, _, _) -> c) cons) (map (\a -> (n, a)) accs)

            let c'' = M.union c' (M.fromList $ consFuncDecls)
            let r'' = M.union r' (M.fromList $ recsFuncDecls)
            let a'' = M.union a' (M.fromList $ accessorFuncDecls)

            mkSortsZ3 TypeMaps {types = (M.insert n da d'), consNamesFuncs = c'', recNamesFuncs = r'', accessorNamesFuncs = a''} s'
        mkSortsZ3 tm [] = return tm

        getAccessors :: TypeMaps -> Sort -> [(Symbol, Sort)] -> Z3 [FuncDecl]
        getAccessors tm d ((sym, ret):xs) = do
            fd <- mkFuncDecl sym [d] ret
            acc <- getAccessors tm d xs
            return (fd:acc)
        getAccessors _ _ [] = return []

mkConstructorZ3 :: TypeMaps -> DataCon -> Z3 (Name, Constructor, [Symbol])
--we need to do something to ensure all symbols are unique... adjust
mkConstructorZ3 d (DataCon n _ tc t) = do
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

numFresh :: Name -> Int -> [Name] -> [Name]
numFresh _ 0 _ = []
numFresh n i ns = let f = fresh n ns in f:numFresh n (i - 1) (f:ns) 

fresh :: Name -> [Name] -> Name
fresh n bads = let maxnum = L.maximum $ 0:(map getnum bads)
               in filter (not . C.isDigit) n ++ show (maxnum + 1)
  where getnum str = let raw = filter C.isDigit str
                     in case raw of
                         [] -> 0
                         xs -> read xs :: Integer
