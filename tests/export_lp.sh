#!/bin/bash

# Test lp export

TIMEFORMAT="%E"
root=`pwd`
lambdapi='dune exec -- lambdapi'

cd tests

outdir=.tmp
#rm -rf $outdir
mkdir -p "$outdir/OK/a b"
cp -f lambdapi.pkg $outdir

# translate lp files
translate() {
    echo translate lp files ...
    for f in OK/*.lp 'OK/a b/escape file.lp'
    do
        out=$outdir/$f
        echo "$f --> $out ..."
        $lambdapi export -o lp -w -v 0 "$f" > "$out"
        if test $? -ne 0; then echo KO; exit 1; fi
    done
}
time translate

# check lp files
check() {
    cd $outdir
    echo check lp files ...
    $lambdapi check -w -v 0 OK/*.lp
    if test $? -ne 0; then echo KO; exit 1; fi
}
time check

cd $root
echo OK
