#!/bin/bash

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"

out=/tmp/lambdapi.output

ok_tests() {
    for f in 'tests/OK/a b/escape file.lp' tests/OK/*.lp tests/OK/*.dk
    do
        case $f in
            tests/OK/why3*.lp);; #FIXME
            *)
                echo lambdapi check $options $f ...
                $lambdapi "$f" > $out 2>&1
                if test $? -ne 0; then cat $out; exit 1; fi;;
        esac
    done
}

ko_tests() {
    echo '############ KO tests ############' 
    for f in tests/KO/*.lp tests/KO/*.dk
    do
        echo lambdapi check $f ...
        $lambdapi "$f" > $out 2>&1
        if test $? -eq 0; then cat $out; exit 1; fi
    done
}

rm -f 'tests/OK/a b/escape file.lpo' tests/OK/*.lpo

echo "############ compile tests/OK files ############"
options='-c -w'
time ok_tests

echo "############ load tests/OK files ############"
options='-w'
time ok_tests
