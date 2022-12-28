#!/bin/sh

echo coqc STTfa.v ...
coqc STTfa.v

echo coqc hol.v ...
coqc hol.v

for f in `ls *.v`
do
    echo coqc $f ...
    coqc $f
done
