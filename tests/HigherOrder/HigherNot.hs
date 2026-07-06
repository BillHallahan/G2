module HigherNot where

type Var = String
data Lit = Pos Var | Neg Var

type Clause = [Lit]
type Clauses = [Clause]

type Model = String -> Bool

checkLit :: Model -> Lit -> Bool
checkLit mdl (Pos v) = mdl v
checkLit mdl (Neg v) = not (mdl v)

checkClause :: Model -> Clause -> Bool
checkClause mdl = any (checkLit mdl)

checkClauses :: Model -> Clauses -> Bool
checkClauses mdl = all (checkClause mdl)

sat1 :: Clauses
sat1 = [ [ Neg "x1", Neg "x2" ]
       ]

check1 :: Model -> Bool
check1 = not . flip checkClauses sat1

sat2 :: Clauses
sat2 = [ [ Pos "x2" ]
       , [ Neg "x1" ]
       ]

check2 :: Model -> Bool
check2 = not . flip checkClauses sat2
