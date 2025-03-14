#!/bin/bash

set -e

echo '############ test export -o raw_dk ############'

root=`pwd`

lambdapi=${LAMBDAPI:-$root/_build/install/default/bin/lambdapi}
dkcheck=${DKCHECK:-dk check}
dkdep=${DKDEP:-dk dep}

TIMEFORMAT="%Es"

outdir=/tmp/export_raw_dk

reset_outdir() {
    rm -rf $outdir
    mkdir -p $outdir
}
reset_outdir

translate() {
    f=tests/OK/${1%.lp}
    out=$outdir/`echo $f | sed -e 's/\//_/g'`
    echo "$f.lp --> $out.dk ..."
    $lambdapi export -w -v 0 -o raw_dk $1 > $out.dk
    if test $? -ne 0; then echo KO; exit 1; fi
}

echo translate files ...
cd tests/OK
for f in *.lp
do
    f=${f%.lp}
    case $f in
        # commutative and non associative symbol
        ac);;
        # unicode character in module name
        π/utf_path);;
        # space in module name
        escape_path|'tests/OK/a b/escape file');;
        # protected symbol in rule LHS argument
        262_private_in_lhs);;
        # dedukti SR algorithm fails
        273|tests/OK/813);;
        # FIXME
        file.with.dot|req.file.with.dot);;
        indind);;
        # "sequential"
        rule_order|813|1033);;
        # "as"
        729);;
        # "notation"
        xor|Set|quant*|Prop|prefix|parametricCoercions|opaque|nat_id*|michael|max-suc-alg|lpparse|861|infix|infer|indrec|implicitArgs[34]|group|cr_qu|cp*|coercions|plus_ac|693|693_assume|679|665|655|655b|649_fo_27|595_and_elim|584_c_slow|579_or_elim_long|579_long_no_duplicate|359|328|245|245b|244|1026|991|706|1101|1190b|1190c|1120);;
        # "quantifier"
        683|650|573|565|430);;
        # nested module name
        require_nondkmident);;
        # proofs
        why3*|tutorial|try|tautologies|rewrite*|remove|natproofs|have|generalize|foo|comment_in_qid|apply|anonymous|admit);;
        # "open"
        triangular|power-fact|postfix|perf_rw_*|not-eager|nonLeftLinear2|natural|Nat|lpparse2|logic|List|FOL|Eq|doc|Bool|arity_var|arity_diff|922|262_pair_ex_2|215|1141|Tactic|Option|String|HOL|Impred|PropExt|Classic|1217|Comp|Pos|Z|1200|lia);;
        # "inductive"
        strictly_positive_*|inductive|989|904|830|341);;
        # underscore in query
        unif_hint|patterns|let|767);;
        # abstracted variable type in rule LHS
        573-2);;
        # domain-free lambda/product
        298_lp|262_parsing|tail|698_abst_impl|330|330b|1035|varmatch|patt|freevars-constraints|eta_equality|declared|boolean|abstractions|303|301|292|225);;
        # opaque definition with no type (https://github.com/Deducteam/Dedukti/issues/319)
        547);;
        # default case:
        *) translate $f.lp;;
    esac
done
cd ../..

check() {
    echo
    echo check translated files ...
    cd $outdir
    #https://github.com/Deducteam/Dedukti/issues/321
    #dk_files=`$dkdep -q -s $dk_files`
    cat > Makefile <<__END__
FILES := \$(wildcard *.dk)
default: \$(FILES:%.dk=%.dko)
%.dko: %.dk
	dk check -e \$<
__END__
    $dkdep -q *.dk >> Makefile
    #echo $dkcheck -q -e $dk_files ...
    #$dkcheck -q -e $dk_files
    make
    res=$?
    cd $root
    if test $res -ne 0; then echo KO; else echo OK; fi
    exit $res
}
check
