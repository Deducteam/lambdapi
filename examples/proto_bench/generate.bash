#!/bin/bash

up_bound=1000

nat_boilerplate="nat.lp"

# Many rules on one symbol
many_symb="many_symb.lp"

cp "$nat_boilerplate" "$many_symb"

echo "symbol f : Nat ⇒ Nat" >> "$many_symb"
echo "rule f 0 → 0" >> "$many_symb"
for i in `seq 1 $up_bound` ; do
    if [[ $(($i % 2)) -eq 0 ]] ; then
        half=$(($i / 2))
        echo "and f $i → $half" >> "$many_symb"
    else
        echo "and f $i → 0" >> "$many_symb"
    fi
done

sum_of_ints="symbol sof : Nat ⇒ Nat
rule sof (S &n) → plus (f (S &n)) (sof &n)"
echo "$sum_of_ints" >> "$many_symb"

echo "compute sof $up_bound" >> "$many_symb"

# Many arguments on one rule
many_args="many_args.lp"
cp "$nat_boilerplate" "$many_args"

ftype=""
nargs=400
for i in {1..nargs}; do
    ftype="Nat ⇒ $ftype"
done
ftype="$ftype""Nat"

cp "$nat_boilerplate" "$many_args"

ftype=""
for i in $(seq 0 $nargs); do
    ftype+="Nat ⇒ "
done
ftype+="Nat"
echo "symbol f : $ftype" >> "$many_args"
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
for i in $(seq 0 $nargs); do
    lhs="$lhs 0"
done
echo "rule f $lhs → 0" >> "$many_args"
for i in $(seq 1 $nargs); do
    lhs=$(all_except_one $i)
    prev=$(( i - 1 ))
    rhs=$(all_except_one $prev)
    echo "and f $lhs → f $rhs" >> "$many_args"
done
echo "compute f $(all_except_one $nargs)" >> "$many_args"
