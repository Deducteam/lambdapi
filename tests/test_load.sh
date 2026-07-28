#!/bin/bash

set -e

lambdapi=_build/install/default/bin/lambdapi
log=/tmp/lambdapi.output
TIMEFORMAT="%Es"

ok_tests() {
    for f in 'tests/OK/a b/escape file.lp' tests/OK/*.lp tests/OK/*.dk
    do
        case $f in
            tests/OK/why3*.lp);; #FIXME
            *)
                echo lambdapi check $option $f ...
                $lambdapi check -w $option "$f" > $log 2>&1 || (cat $log; exit 1)
        esac
    done
}

echo "############ compile tests/OK files ############"
option='-c'
time ok_tests

echo "############ load tests/OK files ############"
option=''
time ok_tests

rm -f 'tests/OK/a b/escape file.lpo' tests/OK/*.lpo
