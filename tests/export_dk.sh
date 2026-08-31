#!/bin/bash

set -e

dune build

echo '############ test export -o dk ############'

lambdapi='../../_build/install/default/bin/lambdapi'
jobs=32
outdir=/tmp/export_dk
TIMEFORMAT="%Es"

reset_outdir() {
    rm -rf $outdir
    mkdir -p $outdir
}
reset_outdir

translate() {
    out=$outdir/${1%.lp}.dk
    echo "$1 --> $out ..."
    $lambdapi export -w -v0 -o dk $1 > $out
    if test $? -ne 0; then echo KO; exit 1; fi
}

echo translate files ...
cd tests/OK
for f in *.lp
do
    f=${f%.lp}
    case $f in
        # FIXME
        file.with.dot|req.file.with.dot|indind|why3*);;
        # takes too much time to check
        perf_rw_engine);;
        # commutative and non associative symbol
        ac);;
        # protected symbol in rule LHS arguments
        262_private_in_lhs);;
        # dedukti SR algorithm fails
        273|813);;
        # require escaped module name
        π/utf_path|escape_path|'a b/escape file'|require_nondkmident|262_pair_ex_2|require_symbol);;
        # use builtin strings
        Tactic);;
        # requires Tactic
        1374|assume|first_hyp|all_hyps|1493);;
        # default case
        *) translate $f.lp;;
    esac
done
cd ../..

check() {
    echo
    echo check translated files ...
    cd $outdir
    echo > Makefile <<__END__
FILES := \$(wildcard *.dk)
default: \$(FILES:%.dk=%.dko)
%.dko: %.dk
	dk check -e \$<
__END__
    dk dep -q *.dk >> Makefile
    make -j$jobs
    res=$?
    if test $res -ne 0; then echo KO; else echo OK; fi
    exit $res
}
time check
