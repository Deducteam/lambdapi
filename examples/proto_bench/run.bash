#!/bin/bash

TIME_PATCH="timing.diff"
PROF_PATCH="gprof.diff"

# Patch to add timing
echo "Patching code"
cd ../..
git apply "examples/proto_bench/$TIME_PATCH"
git apply "examples/proto_bench/$PROF_PATCH"

echo "Compiling"
make
cd "examples/proto_bench"

lp="../../_build/install/default/bin/lambdapi"
for t in *.lp; do
    echo "Checking $t..."
    $lp "$t"
    echo "Profiling"
    gprof "$lp" gmon.out > "$t"'.prof'
done
cd "../.."
echo "Reverting patches"
git apply --reverse "examples/proto_bench/$TIME_PATCH"
git apply --reverse "examples/proto_bench/$PROF_PATCH"

