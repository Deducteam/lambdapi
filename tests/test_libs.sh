#!/bin/bash

set -e

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"

checkoutLib() {
    git clone $1 $2
}

test_Lib() {
    for f in $(find $1 -name *.lp)  $(find $1 -name *.dk)
    do
        echo lambdapi check $options $f ...
        $lambdapi $options "$f"
    done
}

checkoutLib $1 $2
options='-w'
time test_Lib $2
