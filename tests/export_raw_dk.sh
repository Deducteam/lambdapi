#!/bin/bash

echo '############ test export -o raw_dk ############'

lambdapi=${LAMBDAPI:-_build/install/default/bin/lambdapi}
dkcheck=${DKCHECK:-dk check}
dkdep=${DKDEP:-dk dep}

TIMEFORMAT="%Es"

root=`pwd`

outdir=/tmp/export_raw_dk

reset_outdir() {
    rm -rf $outdir
    mkdir -p $outdir
}
reset_outdir

# compute lp files to test
cd tests/OK
for f in *.lp
do
    f=${f%.lp}
    case $f in
        ac);; # because dedukti does not handle commutative and non associative symbols
        π/utf_path);; # because dedukti does not accept unicode characters in module names
        escape_path|'tests/OK/a b/escape file');; # because dedukti does not accept spaces in module names
        262_private_in_lhs);; # because dedukti does not accept protected symbols in rule LHS arguments
        273|tests/OK/813);; # because dedukti SR algorithm fails
        file.with.dot|req.file.with.dot);; #FIXME
        indind);; #FIXME
        rule_order);; #because it contains sequential
        xor|Set|quant*|Prop|prefix|parametricCoercions|opaque|nat_id*|michael|max-suc-alg|lpparse);; #because it contains notation
        require_nondkmident);; #because it uses a nested module name
        why3*|tutorial|try|tautologies|rewrite*|remove|natproofs);; #because it contains proofs
        triangular|power-fact|postfix|perf_rw_*|not-eager|nonLeftLinear2|natural|Nat|lpparse2);; #because it contains open
        plus_ac);; #because it contains associative or commutative alone
        strictly_positive_*);; #because it contains inductive
        *) lp_files="tests/OK/$f.lp $lp_files";
           f=`echo $f | sed -e 's/\//_/g'`;
           dk_files="tests/OK/$f.dk $dk_files";;
    esac
done
cd ../..

# compile lp files
compile() {
    echo 'compile lp files ...'
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
    echo 'translate lp files ...'
    for f in $lp_files
    do
        f=${f%.lp}
        out=$outdir/`echo $f | sed -e 's/\//_/g'`
        echo "$f.lp --> $out.dk ..."
        $lambdapi export -w -v 0 -o raw_dk $f.lp > $out.dk
        if test $? -ne 0; then echo KO; exit 1; fi
    done
}
time translate

# check dk files
check() {
    cd $outdir
    echo 'remove #REQUIRE commands (to be removed when https://github.com/Deducteam/Dedukti/issues/262 is fixed) ...'
    sed -i -e 's/#REQUIRE.*$//' $dk_files
    dk_files=`$dkdep -q -s $dk_files`
    echo $dkcheck -q -e $dk_files ...
    $dkcheck -q -e $dk_files
    res=$?
    cd $root
    if test $res -ne 0; then echo KO; else echo OK; fi
    exit $res
}
time check
