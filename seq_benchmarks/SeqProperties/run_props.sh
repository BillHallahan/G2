
build_with() {
    cabal build --ghc-options="-fplugin-opt=G2.Plugin:\"--time 60 --solver-time --print-sol-counts --smt $1  --smt-timeout 5 $2 --logs-folder logs_$3\""
}

build_with_seq() {
    build_with $1 "--smt-lists --smt-strings $2" "$1$2"
}


build_with_seq "z3" ""
build_with_seq "cvc5" ""
build_with_seq "cvc5,z3" ""
build_with_seq "cvc5,z3" "--no-string-simplifier"
build_with "cvc5,z3" "" "_concrete"
