#!/usr/bin/env fish

set dir $argv[1]
echo $dir
cd $dir

rm -rf */*-graded
rm -rf */HW*
rm -rf */Hw*
rm -rf */hw*

# for d in *
#     if tar tzf $d/*/final.tar.gz | grep liquid-cache >/dev/null
#         echo $d
#     end
# end

## anonymize folders
#
# extract final.tar.gz from individual student
# submissions and give a unique id to each
set i 0
for d in *
    echo $d

    # grab the last submission in case of multiple
    set tgzs $d/*/final.tar.gz
    if test (count $tgzs) -gt 0
        set tgz $tgzs[(count $tgzs)]

        tar xzf $tgz
        rm -rf final/*.lhs final/.liquid
        rm -f final/.DS_Store final/._.DS_Store final/liquid-cache/.DS_Store final/liquid-cache/._.DS_Store
        if test -d final/liquid-cache/; and test (count (ls final/liquid-cache/)) -gt 0
            for lhs in  final/liquid-cache/*
                # remove any lines that might contain a name, email, or id
                perl -ni -e 'print unless /(name|email|id)\s*(\=|\:)/i' $lhs
                # make sure the file has a .lhs extension..
                mv $lhs $lhs.lhs
            end
            tar czf (printf "%02d" $i).tar.gz final
            set i (expr $i + 1)
            rm -rf final
        end
    end

    # clean up
    rm -rf $d
end

# ## anonymize files
# #
# for f in *
#     echo $f
#     tar xzf $f
#     for lhs in final/*.lhs
#         ruby -i -ne 'print if not /(name|email|id)\s*(\=|\:)/i' $lhs
#     end
#     for lhs in  final/liquid-cache/*
#         ruby -i -ne 'print if not /(name|email|id)\s*(\=|\:)/i' $lhs
#     end
#     tar czf $f final
#     rm -r final
# end
