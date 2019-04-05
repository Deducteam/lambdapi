#!/bin/bash

# Currently generates two test files
# + many_sym.lp
# + many_args.lp

nat_boilerplate="nat.lp"

# Many rules on one symbol
nrules=1000
fname="many_symb.lp"
# Use the nat template
cp "$nat_boilerplate" "$fname"

echo "symbol f : Nat ⇒ Nat" >> "$fname"
# Define rules: if n pair, f n → n /2 else f n → 0
echo "rule f 0 → 0" >> "$fname"
for i in $(seq 1 $nrules) ; do
    if [[ $(($i % 2)) -eq 0 ]] ; then
        half=$(($i / 2))
        echo "and f $i → $half" >> "$fname"
    else
        echo "and f $i → 0" >> "$fname"
    fi
done
# Define function summing values of f
sum_of_effs="symbol sof : Nat ⇒ Nat
rule sof (S &n) → plus (f (S &n)) (sof &n)"
echo "$sum_of_effs" >> "$fname"

# Computation
echo "compute sof $nrules" >> "$fname"


## Many arguments on one rule
## Generate a file with a symbol having rules with many arguments
## a rule is 'f 0 0 ... 0 i 0 ... 0 → f 0 0 ... (i - 1) 0 ... 0'
## with [i] at the index [i] in the sequence of zeros, and the first rule is
## f 0 ... 0 → 0
fname="many_args.lp"
cp "$nat_boilerplate" "$fname"

ftype=""
nargs=400
for i in {1..nargs}; do
    ftype="Nat ⇒ $ftype"
done
ftype="$ftype""Nat"

cp "$nat_boilerplate" "$fname"

ftype=""
for i in $(seq 0 $nargs); do
    ftype+="Nat ⇒ "
done
ftype+="Nat"
echo "symbol f : $ftype" >> "$fname"
# [all_except_one i] returns a line of zeros with [i] at the [i]th
# position
function all_except_one {
    local args=""
    for i in $(seq 1 $1); do
        args+=" 0"
    done
    args+=" $1 "
    for i in $(seq $((1 + $1)) $nargs); do
        args+=" 0"
    done
    echo $args
}
# Initial rule
for i in $(seq 0 $nargs); do
    lhs="$lhs 0"
done
echo "rule f $lhs → 0" >> "$fname"
# Other rules
for i in $(seq 1 $nargs); do
    lhs=$(all_except_one $i)
    prev=$(( i - 1 ))
    rhs=$(all_except_one $prev)
    echo "and f $lhs → f $rhs" >> "$fname"
done
# computation
echo "compute f $(all_except_one $nargs)" >> "$fname"
