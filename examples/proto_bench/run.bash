#!/bin/bash

set -o noclobber
GITROOT="../../"
FROMGIT="examples/proto_bench"
PROFILING=''

while [[ "$1" =~ ^- && ! "$1" == "--" ]]; do
    case $1 in
        -p | --prof )
            shift; PROFILING=yes
            ;;
    esac; shift
done
if [[ "$1" == '--' ]]; then shift; fi

TIME_PATCH="timing.diff"
PROF_PATCH="gprof.diff"

# Patch to add timing
echo "Patching code"
cd "$GITROOT"
git apply "examples/proto_bench/$TIME_PATCH"
if [[ -n $PROFILING ]]; then
    git apply "examples/proto_bench/$PROF_PATCH"
fi

echo "Compiling"
make
cd "$FROMGIT"

lp="../../_build/install/default/bin/lambdapi"
for t in *.lp; do
    echo "Checking $t..."
    $lp "$t"
    if [[ -n $PROFILING ]]; then
        echo "Profiling"
        if [[ -e "$t"'.prof' ]]; then
            rm "$t"'.prof'
        fi
        gprof "$lp" gmon.out > "$t"'.prof'
    fi
done
cd "$GITROOT"
echo "Reverting patches"
git apply --reverse "examples/proto_bench/$TIME_PATCH"
if [[ -n $PROFILING ]]; then
    git apply --reverse "examples/proto_bench/$PROF_PATCH"
fi

## Clean generatated files
cd "$FROMGIT"
for f in _autogen*; do
    rm "$f"
done
