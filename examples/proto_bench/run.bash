#!/bin/bash

TIME_PATCH="timing.patch"

# Patch to add timing
echo "Patching code"
cd ../..
git apply "examples/proto_bench/$TIME_PATCH"

echo "Compiling"
make
cd "examples/proto_bench"
lp="../../_build/install/default/bin/lambdapi"
for t in *.lp; do
    exec "$lp" "$t"
done
cd "../.."
git apply --reverse "examples/proto_bench/$TIME_PATCH"

