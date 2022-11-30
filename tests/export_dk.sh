#!/bin/bash

echo '############ test export -o dk ############'

TIMEFORMAT="%Es"
root=`pwd`
lambdapi='dune exec -- lambdapi'

# compute lp files to test
dir=tests/OK
outdir=/tmp/`echo $dir | sed -e 's/\//_/g'`
cd $dir
for f in *.lp
do
    f=${f%.lp}
    case $f in
        ac);; # because dedukti does not handle commutative and non associative symbols
        π/utf_path);; # because dedukti does not accept unicode characters in module names
        escape_path|'a b/escape file');; # because dedukti does not accept spaces in module names
        262_private_in_lhs);; # because dedukti does not accept protected symbols in rule LHS arguments
        273|813);; # because dedukti SR algorithm fails
        file.with.dot|req.file.with.dot);; #FIXME
        indind);; #FIXME
        why3*);; #FIXME
        *) lp_files="$dir/$f.lp $lp_files";
           f=`echo $f | sed -e 's/\//_/g'`;
           dk_files="${outdir}_$f.dk $dk_files";
           dko_files="${outdir}_$f.dko $dko_files";;
    esac
done

# compile lp files (optional)
compile() {
    cd $root
    echo 'compile lp files (optional) ...'
    #$lambdapi check -w -c $lp_files # does not work because of #802
    for f in $lp_files
    do
        echo "compile $f ..."
        $lambdapi check -w -v 0 -c $f
    done
}
#time compile

# translate lp files to dk files
translate() {
    cd $root
    echo 'translate lp files ...'
    for f in $lp_files
    do
        f=${f%.lp}
        out=/tmp/`echo $f | sed -e 's/\//_/g'`
        echo "$f.lp --> $out.dk ..."
        $lambdapi export -w -v 0 -o dk $f.lp > $out.dk
        if test $? -ne 0; then echo KO; exit 1; fi
    done
}
time translate

# check dk files
check() {
    cd /tmp/
    echo 'remove #REQUIRE commands (to be removed when https://github.com/Deducteam/Dedukti/issues/262 is fixed) ...'
    sed -i -e 's/#REQUIRE.*$//' $dk_files    
    echo check dk files using `which ${DKCHECK:-dk}` ...
    ${DKCHECK:-dk check} -q -e `${DKDEP:-dk dep} -q -s $dk_files`
    if test $? -ne 0; then echo KO; exit 1; fi
}
time check

echo OK
cd $root
