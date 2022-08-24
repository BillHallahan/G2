## G2 Haskell Symbolic Execution Engine
---
#### About
G2 performs lazy symbolic execution of Haskell programs to detect state reachability.
It is capable of generating assertion failure counterexamples and solving for higher-order functions.

---

#### Dependencies
* GHC 8.2.2, 8.6.5, or 8.10.7: https://www.haskell.org/ghc/
* Custom Haskell Standard Library: https://github.com/BillHallahan/base-4.9.1.0
* Z3 SMT Solver: https://github.com/Z3Prover/z3

---
#### Setup:
1) Install GHC 8.2.2, 8.6.5, or 8.10.7.
2) Install Z3.  Ensure Z3 is in your system's path.
3) Pull the Custom Haskell Standard Library into ~/.g2 by running `bash base_setup.sh`.

---
#### Command line:

###### Reachability:

`cabal run G2 ./tests/Samples/Peano.hs add`

###### LiquidHaskell:

`cabal run G2 -- --liquid ./tests/Liquid/Peano.hs --liquid-func add`

###### Arguments:

* `--n` number of reduction steps to run
* `--max-outputs` number of inputs/results to display
* `--smt` Pass "z3" or "cvc4" to select a solver [Default: Z3]
* `--time` Set a timeout in seconds

---

#### Authors
* Bill Hallahan (Yale)
* Anton Xue (Yale)
* Maxwell Troy Bland (UCSD)
* Ranjit Jhala (UCSD)
* Ruzica Piskac (Yale)
