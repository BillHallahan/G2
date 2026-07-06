module SAT where

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
sat1 = [ [ Pos "x1", Pos "x2", Pos "x3" ]
       , [ Neg "x1", Neg "x2" ]
       , [ Pos "x1" ]
       , [ Pos "x2", Neg "x3" ]
       , [ Pos "y", Pos "a", Pos "bcd" ]
       , [ Neg "y", Neg "a" ]
       , [ Pos "y" ]
       , [ Pos "a", Neg "bcd" ]
       ]

sat2 :: Clauses
sat2 = [ [ Pos "x1", Neg "x2", Pos "x3" ]
       , [ Pos "x1", Pos "x2" ]
       , [ Neg "x1" ]
       , [ Neg "x2", Neg "x3" ]
       , [ Pos "y", Pos "a", Pos "bcd" ]
       , [ Neg "y", Neg "a" ]
       , [ Pos "y" ]
       , [ Pos "a", Neg "bcd" ]
    ]

checkSat1 :: Model -> Bool
checkSat1 = not . flip checkClauses sat1

checkSat2 :: Model -> Bool
checkSat2 = not . flip checkClauses sat1