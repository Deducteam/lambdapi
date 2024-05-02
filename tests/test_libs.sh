#!/bin/bash

set -e

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"

out=/tmp/lambdapi.output

checkout_lib() {
    git clone $1 $2
}

test_Lib() {
    for f in $(find $1 -name *.lp)  $(find $1 -name *.dk)
    do
        echo lambdapi check $options $f ...
        $lambdapi $options "$f" > $out 2>&1
    done
}

checkout_lib $1 $2
options='-w'
time test_Lib $2
