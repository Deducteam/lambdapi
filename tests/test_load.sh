#!/bin/bash

set -e

root=`pwd`
lambdapi=${LAMBDAPI:-$root/_build/install/default/bin/lambdapi}
TIMEFORMAT="%Es"
out=/tmp/lambdapi.output

ok_tests() {
    for f in 'tests/OK/a b/escape file.lp' tests/OK/*.lp tests/OK/*.dk
    do
        case $f in
            tests/OK/why3*.lp);; #FIXME
            *)
                echo lambdapi check $options $f ...
                $lambdapi check "$f" > $out 2>&1 || (cat $out; exit 1)
        esac
    done
}

rm -f 'tests/OK/a b/escape file.lpo' tests/OK/*.lpo

echo "############ compile tests/OK files ############"
options='-c -w'
time ok_tests

echo "############ load tests/OK files ############"
options='-w'
time ok_tests
