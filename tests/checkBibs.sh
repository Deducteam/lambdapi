#!/bin/bash

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"
out=/tmp/lambdapi.output

checkoutLib() {
    git clone $1 $2
}

checkLib() {
    for f in $(find $1 -name *.lp)
    do
        echo lambdapi check $options $f ...
        $lambdapi "$f" > $out 2>&1
        if test $? -ne 0; then cat $out; exit 1; fi;
    done
}

checkoutLib $1 $2
options='-w'
checkLib $2
