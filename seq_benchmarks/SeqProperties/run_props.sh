
build_with() {
    cabal build --ghc-options="-fplugin-opt=G2.Plugin:\"--print-sol-counts --smt $1 --logs-folder logs_$1\""
}

build_with "z3"
build_with "cvc5"
build_with "cvc5,z3"