#!/bin/bash

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"

out=/tmp/lambdapi.output

ok_tests() {
    echo "############ OK tests$header ############" 
    for f in 'tests/OK/a b/escape file.lp' tests/OK/*.lp tests/OK/*.dk
    do
        echo lambdapi check $options $f ...
        $lambdapi "$f" > $out 2>&1
        if test $? -ne 0; then cat $out; exit 1; fi
    done
}
rm -f 'tests/OK/a b/escape file.lpo' tests/OK/*.lpo
time ok_tests
options='-c'
header=" with options: $options"
time ok_tests

ko_tests() {
    echo '############ KO tests ############' 
    for f in tests/KO/*.lp tests/KO/*.dk
    do
        echo lambdapi check $f ...
        $lambdapi "$f" > $out 2>&1
        if test $? -eq 0; then cat $out; exit 1; fi
    done
}
time ko_tests
