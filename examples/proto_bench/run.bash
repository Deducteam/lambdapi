#!/bin/bash

set -o noclobber
GITROOT="../../"
FROMGIT="examples/proto_bench"

TIME_PATCH="timing.diff"
PROF_PATCH="gprof.diff"

# Patch to add timing
echo "Patching code"
cd "$GITROOT"
git apply "examples/proto_bench/$TIME_PATCH"
git apply "examples/proto_bench/$PROF_PATCH"

echo "Compiling"
make
cd "$FROMGIT"

lp="../../_build/install/default/bin/lambdapi"
for t in *.lp; do
    echo "Checking $t..."
    $lp "$t"
    echo "Profiling"
    if [[ -e "$t"'.prof' ]]; then
        rm "$t"'.prof'
    fi
    gprof "$lp" gmon.out > "$t"'.prof'
done
cd "$GITROOT"
echo "Reverting patches"
git apply --reverse "examples/proto_bench/$TIME_PATCH"
git apply --reverse "examples/proto_bench/$PROF_PATCH"

## Clean generatated files
cd "$FROMGIT"
for f in _autogen*; do
    rm "$f"
done
