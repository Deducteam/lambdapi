#!/bin/bash

set -e

lambdapi='dune exec -- lambdapi check'
TIMEFORMAT="%Es"

out=/tmp/lambdapi.output

checkout_lib() {
    IFS='/' read -ra ADDR <<< "$1"
    repo_name="${ADDR[-1]}"
    IFS='.' read -ra ADDR <<< "$repo_name"
    repo_name="${ADDR[0]}"
    git clone $1 $repo_name
}

test_Lib() {
    for f in $(find $1 -name *.lp)  $(find $1 -name *.dk)
    do
        echo lambdapi check $options $f ...
        $lambdapi $options "$f" > $out 2>&1
    done
}

checkout_lib $1
options='-w'
time test_Lib $repo_name
