
build_with() {
    cabal build --ghc-options="-fplugin-opt=G2.Plugin:\"--time 300 --solver-time --print-sol-counts --smt $1  --smt-timeout 5 $2 --logs-folder logs_$3\"" > solver_logs/$3.txt
}

build_with_seq() {
    build_with $1 "--smt-lists --smt-strings $2" "$1$2"
}

mkdir -p solver_logs

build_with_seq "z3" ""
build_with_seq "cvc5" ""

build_with_seq "cvc5,z3" ""

build_with_seq "cvc5,z3" "--no-string-simplifier"
build_with_seq "cvc5,z3" "--no-unsat-list-solver"
build_with_seq "cvc5,z3" "--no-string-simplifier --no-unsat-list-solver"

build_with "cvc5,z3" "--only-run-in DefinitionsFalse,EquivFalse,IsaplannerFalse,ProdFalse" "_concrete"
