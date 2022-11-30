#!/bin/bash

echo '############ test export -o lp ############'

TIMEFORMAT="%Es"
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
        case $f in
            OK/why3*.lp);; #FIXME
            *) out=$outdir/$f
               echo "$f --> $out ..."
               $lambdapi export -o lp -w -v 0 "$f" > "$out"
               if test $? -ne 0; then echo KO; exit 1; fi
        esac
    done
}
time translate

# check lp files
check() {
    cd $outdir
    echo check lp files ...
    for f in OK/*.lp 'OK/a b/escape file.lp'
    do
        case $f in
            OK/why3*.lp);; #FIXME
            *) echo "lambdapi check $f ..."
               $lambdapi check -w -v 0 "$f"
               if test $? -ne 0; then echo KO; exit 1; fi
        esac
    done
}
time check

cd $root
echo OK
