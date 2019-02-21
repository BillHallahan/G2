echo "cabal run G2 paper_examples/ paper_examples/Intersect.hs intersect_prop -- --returns-true"
echo "Finds a counterexample to intersect_prop, from Section 2.1, in paper_examples/Intersect.hs."
cabal run G2 paper_examples/ paper_examples/Intersect.hs intersect_prop -- --returns-true

echo "------------------------------"
echo ""

echo "cabal run G2 paper_examples/ paper_examples/Repl.hs repl_prop -- --returns-true"
echo "Finds a counterexample to repl_prop, from Figure 2, in paper_examples/Repl.hs."
cabal run G2 paper_examples/ paper_examples/Repl.hs repl_prop -- --returns-true

echo "------------------------------"
echo ""

echo "cabal run G2 paper_examples/ -- --liquid paper_examples/Zip.hs --liquid-func zip"
echo "Finds a counterexample to zip's refinement type, from Section 2.4, in paper_examples/Zip.hs."
cabal run G2 paper_examples/ -- --liquid paper_examples/Zip.hs --liquid-func zip

echo "------------------------------"
echo ""

echo "cabal run G2 paper_examples/ -- --liquid paper_examples/Concat.hs --liquid-func concat --cut-off 100"
echo "Finds a counterexample to concat's refinement type, from Section 2.5, in paper_examples/Concat.hs."
cabal run G2 paper_examples/ -- --liquid paper_examples/Concat.hs --liquid-func concat --cut-off 100

echo "------------------------------"
echo ""

echo "cabal run G2 paper_examples/ -- --liquid paper_examples/Replicate.hs --liquid-func replicate --cut-off 100"
echo "Finds a counterexample to replicate's refinement type, from the end of Section 6.2, in paper_examples/Replicate.hs."
cabal run G2 paper_examples/ -- --liquid paper_examples/Replicate.hs --liquid-func replicate --cut-off 100
