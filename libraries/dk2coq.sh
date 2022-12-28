#!/bin/sh

for f in *.dk
do
    b=`basename $f .dk`
    echo "lambdapi export -o stt_coq $b.dk"
    lambdapi export -o stt_coq $b.dk > $b.v || exit 1
done
