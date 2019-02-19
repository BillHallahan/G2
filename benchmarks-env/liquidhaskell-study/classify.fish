#!/usr/bin/env fish

set dir $argv[1]
cd $dir

rm -rf final safe unsafe error
mkdir safe unsafe error

for tgz in *.tar.gz
    tar xzf $tgz
    set lhss final/liquid-cache/*List*.lhs final/liquid-cache/*MapReduce*.lhs final/liquid-cache/*KMeans*.lhs
    echo $tgz "[" (count $lhss) "files" "]"
    for lhs in $lhss
        stack exec liquid -- $lhs > $lhs.log 2>&1
        switch $status
        case 0
            cp $lhs     safe/(basename $lhs)
            cp $lhs.log safe/(basename $lhs).log
        case 1
            cp $lhs     unsafe/(basename $lhs)
            cp $lhs.log unsafe/(basename $lhs).log
        case '*'
            cp $lhs     error/(basename $lhs)
            cp $lhs.log error/(basename $lhs).log
        end
        echo -n .
    end
    echo ''
    rm -rf final
end
