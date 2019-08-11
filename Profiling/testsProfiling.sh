#!/bin/bash 

# edit if needed
TestsDir="./Profiling/Tests"
ProfilesDir="./Profiling/Profiles"

mkdir -p $ProfilesDir 

validated=()
not_validated=()

function cabal_run {
	cabal run G2 $TestsDir/$1 $2 -- --n $3 $4 --merge-states --validate
}

function test {
	Test=$1
	echo "-----"
	echo "$Test"
	res=$(cabal run G2 $TestsDir/$2 $3 -- --n $4 $5 --merge-states --validate)
	echo $res

	if [[ $res == *"Validated"* ]]; then
  		validated+=($1)
  	else
  		notvalidated+=($1)
	fi

	cp G2.prof "$ProfilesDir"/"$Test".prof

}

test "reverse" "MiscOrganized.hs" "reverse'" "1000"

# Test="reverse"
# echo "-----"
# echo "$Test" 
# cabal run G2 "$TestsDir"/MiscOrganized.hs reverse\' -- --n 1000 --merge-states --validate
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "compress" "MiscOrganized.hs" "compress" "1000"

# Test="compress"
# echo "-----"
# echo "$Test" 
# cabal run G2 "$TestsDir"/MiscOrganized.hs compress -- --n 1000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "Peano_add_assert_equalsFour" "Peano.hs" "add" "800" "--assert equalsFour"

# Test="Peano_add_assert_equalsFour"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/Peano.hs add -- --n 800 --assert "equalsFour" --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "Peano_add_assert_equalsFour_assume_multiplyToFour" "Peano.hs" "add" "1500" "--assume multiplyToFour --assert equalsFour"

# Test="Peano_add_assert_equalsFour_assume_multiplyToFour"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/Peano.hs add -- --n 1500 --assume "multiplyToFour" --assert "equalsFour" --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "Peano_add_assert_fstIsTwo_assume_fstIsEvenAddToFour" "Peano.hs" "add" "2500" "--assume fstIsEvenAddToFour --assert fstIsTwo"

# Test="Peano_add_assert_fstIsTwo_assume_fstIsEvenAddToFour"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/Peano.hs add -- --n 2500 --assume "fstIsEvenAddToFour" --assert "fstIsTwo" --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "appendOneStart_assert_appendOneStartAss" "MiscOrganized.hs" "appendOneStart" "2000" "--assert appendOneStartAss"

# Test="appendOneStart_assert_appendOneStartAss"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/MiscOrganized.hs appendOneStart -- --n 2000 --assert appendOneStartAss --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "appendOneEnd_assert_appendOneEndAss" "MiscOrganized.hs" "appendOneEnd" "800" "--assert appendOneEndAss"

# Test="appendOneEnd_assert_appendOneEndAss"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/MiscOrganized.hs appendOneEnd -- --n 800 --assert appendOneEndAss --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "treeSum" "ManyPathsOneDataCon.hs" "treeSum" "1000"

# Test="treeSum"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs treeSum -- --n 1000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "lastSums" "ManyPathsOneDataCon.hs" "lastSums" "2000"

# Test="lastSums"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs lastSums -- --n 2000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "maybeLastSnd" "ManyPathsOneDataCon.hs" "maybeLastSnd" "1000"

# Test="maybeLastSnd"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs maybeLastSnd -- --n 1000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "sumIfAny" "ManyPathsOneDataCon.hs" "sumIfAny" "2000"

# Test="sumIfAny"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs sumIfAny -- --n 2000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "foldrTest" "ManyPathsOneDataCon.hs" "foldrTest" "2000"

# Test="foldrTest"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs foldrTest -- --n 2000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "subseqOfTest" "ManyPathsOneDataCon.hs" "subseqOfTest" "900"

# Test="subseqOfTest"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs subseqOfTest -- --n 900 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "filter_sumEvens" "ManyPathsOneDataCon.hs" "sumEvens" "2000"

# Test="filter_sumEvens"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs sumEvens -- --n 2000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

test "buried_add" "ManyPathsOneDataCon.hs" "add" "3000"

# Test="buried_add"
# echo "-----"
# echo "$Test"
# cabal run G2 "$TestsDir"/ManyPathsOneDataCon.hs add -- --n 3000 --merge-states
# cp G2.prof "$ProfilesDir"/"$Test".prof

echo "Validated:"
printf "%s\n" "${validated[@]}"

echo "Not Validated:"
printf "%s\n" "${not_validated[@]}"
