#!/bin/bash

set -e

lambdapi='dune exec -- lambdapi check'
options='-w'
TIMEFORMAT="%Es"

out=/tmp/lambdapi.output

checkout_lib() {
    IFS='/' read -ra ADDR <<< "$1"
    repo_path="${ADDR[-1]}"
    IFS='.' read -ra ADDR <<< "$repo_path"
    repo_path="/tmp/${ADDR[0]}"
    if [ -d "$repo_path" ] ; then
        rm -fr "$repo_path"
    fi
    git clone $1 $repo_path
}

test_lib() {
    for f in $(find $1 -name '*.lp' -o -name '*.dk')
    do
        echo lambdapi check $options $f ...
        $lambdapi "$f" > $out 2>&1 || (cat $out; exit 1)
    done
}

checkout_lib $1
time test_lib $repo_path
