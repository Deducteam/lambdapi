#!/bin/bash

set -e

echo '############ test export -o dk ############'

root=`pwd`

lambdapi=${LAMBDAPI:-$root/_build/install/default/bin/lambdapi}
dkcheck=${DKCHECK:-dk check}
dkdep=${DKDEP:-dk dep}

TIMEFORMAT="%Es"

outdir=/tmp/export_dk

reset_outdir() {
    rm -rf $outdir
    mkdir -p $outdir
}
reset_outdir

translate() {
    f=tests/OK/${1%.lp}
    out=$outdir/`echo $f | sed -e 's/\//_/g'`
    echo "$f.lp --> $out.dk ..."
    $lambdapi export -w -v 0 -o dk $1 > $out.dk
    if test $? -ne 0; then echo KO; exit 1; fi
}

echo translate files ...
cd tests/OK
for f in *.lp
do
    f=${f%.lp}
    case $f in
        # commutative and non associative symbol
        ac);;
        # protected symbol in rule LHS arguments
        262_private_in_lhs);;
        # dedukti SR algorithm fails
        273|813);;
        # FIXME
        file.with.dot|req.file.with.dot);;
        indind);;
        why3*);;
        # require escaped module name
        π/utf_path|escape_path|'a b/escape file'|require_nondkmident);;

        # default case
        *) translate $f.lp;;
    esac
done
cd ../..

check() {
    echo
    echo check translated files ...
    cd $outdir
    #https://github.com/Deducteam/Dedukti/issues/321
    #dk_files=`$dkdep -q -s $dk_files`
    echo > Makefile <<__END__
FILES := \$(wildcard *.dk)
default: \$(FILES:%.dk=%.dko)
%.dko: %.dk
	dk check -e \$<
__END__
    $dkdep -q *.dk >> Makefile
    #echo $dkcheck -q -e $dk_files ...
    #$dkcheck -q -e $dk_files
    make
    res=$?
    cd $root
    if test $res -ne 0; then echo KO; else echo OK; fi
    exit $res
}
time check
