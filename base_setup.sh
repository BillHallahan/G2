get_base() {
	if [ ! -d $2 ] ; then
	    git clone $1 $2
	else
	    cd "$2"
	    git pull $1
	fi
}

get_base "https://github.com/BillHallahan/base-4.9.1.0.git" ~/.g2/base-4.9.1.0/
get_base "https://github.com/BillHallahan/G2Stubs.git" ~/.g2/G2Stubs/