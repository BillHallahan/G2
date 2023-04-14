base_commit=b96cddf
stubs_commit=3908605

get_base() {
	printf "Updating $2\n"
    cd "$2"
	if [ ! -d $2 ] ; then
	    git clone $1 $2 &> /dev/null
	else
		git checkout master &> /dev/null
	    git pull $1 &> /dev/null
	fi
	git checkout $3 &> /dev/null
}

get_base "https://github.com/BillHallahan/base-4.9.1.0.git" ~/.g2/base-4.9.1.0/ $base_commit
get_base "https://github.com/BillHallahan/G2Stubs.git" ~/.g2/G2Stubs/ $stubs_commit