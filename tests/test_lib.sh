#!/bin/bash

set -e

lambdapi='dune exec -- lambdapi check'
options='-w'
TIMEFORMAT="%Es"

checkout_lib() {
    IFS='/' read -ra ADDR <<< "$1"
    repo_name="${ADDR[-1]}"
    IFS='.' read -ra ADDR <<< "$repo_name"
    repo_name="/tmp/${ADDR[0]}"
    git clone $1 $repo_name
}

test_lib() {
    for f in $(find $1 -name *.lp)  $(find $1 -name *.dk)
    do
        echo lambdapi check $options $f ...
        $lambdapi $options "$f"
    done
}

checkout_lib $1
time test_lib $repo_name
