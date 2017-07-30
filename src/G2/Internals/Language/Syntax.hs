module G2.Internals.Language.Syntax
    ( module G2.Internals.Language.Syntax
    ) where


-- | Variables, data constructors, type variables, and type constructors.
data NameSpace = VarNSpace | DataNSpace | TvNSpace | TcClsNSpace
               deriving (Show, Eq, Read, Ord)

-- | The occurrence name is defined as a string, with a `Maybe` module name
-- appearing. The `Int` denotes a `Unique` translated from GHC. For instance,
-- in the case of @Map.empty@, the occurrence name is @"empty"@, while the
-- module name is some variant of @Just \"Data.Map\"@.
data Name = Name String (Maybe String) NameSpace Int
          deriving (Show, Eq, Read, Ord)

data Id = Id Name Type deriving (Show, Eq, Read)

data Expr = Var  Id
          | Lit  Literal
          | Prim Primitive
          | Data DataCon
          | App  Expr Expr
          | Lam  Id Expr
          | Let  Binding Expr
          | Case Expr Id [Alt]
          | Type Type
          deriving (Show, Eq, Read)

data Primitive = PTRUE | PFALSE
               | PGE | PGT | PEQ | PLT | PLE
               | PAND | POR | PNOT | PImplies
               | PPlus | PMinus | PMult | PDiv
               | PAssert | PAssume
               deriving (Show, Eq, Read)

data Literal = LitInt    Int
             | LitFloat  Float
             | LitDouble Rational
             | LitChar   Char
             | LitString String
             deriving (Show, Eq, Read)

data DataCon = DataCon Name Type [Type]
             | PrimCon PrimDataCon
             deriving (Show, Eq, Read)

data PrimDataCon = I | D | F | C | PTrue | PFalse deriving (Show, Eq, Read)

data RecForm = Rec | NonRec deriving (Show, Eq, Read)

data Binding = Binding RecForm [(Id, Expr)] deriving (Show, Eq, Read)

data AltCon = DataAlt DataCon
            | Default
            deriving (Show, Eq, Read)

data Alt = Alt AltCon [Id] Expr deriving (Show, Eq, Read)

data TyBinder = AnonTyBndr
              | NamedTyBndr Name
              deriving (Show, Eq, Read)

data Type = TyVarTy Name
          | TyInt | TyFloat | TyDouble | TyChar | TyString | TyBool
          | TyLitInt | TyLitFloat | TyLitDouble | TyLitChar | TyLitString
          | TyFun Type Type
          | TyApp Type Type
          | TyConApp TyCon [Type]
          | TyForAll TyBinder Type
          | Bottom
          deriving (Show, Eq, Read)

data TyCon = FunTyCon     Name [TyBinder]
           | AlgTyCon     Name [Name] AlgTyRhs
           | SynonymTyCon Name [Name]
           | FamilyTyCon  Name [Name]
           | PrimTyCon    Name [TyBinder]
           | Promoted     Name [TyBinder] DataCon
           deriving (Show, Eq, Read)

data AlgTyRhs = AbstractTyCon Bool
              | DataTyCon     [Name]
              | NewTyCon      Name
              | TupleTyCon    Name
              deriving (Show, Eq, Read)

