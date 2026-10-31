#!/bin/bash

set -e

echo '############ test export -o dk ############'

dir=/tmp/export_raw_dk
rm -rf $dir
mkdir -p $dir

pwd > $dir/SRC

cd tests/OK
ls -1 *.lp > $dir/FILES

exclude () {
    for f in $*
    do
        if test -f $f.lp
        then
            sed -i -e "/$f/d" $dir/FILES
        else
            echo unknown file: $f.lp
            exit 1
        fi
    done
}

# FIXME
exclude file.with.dot req.file.with.dot indind
# takes too much time to check
exclude perf_rw_engine
# commutative and non associative symbol
exclude ac
# invalid module name
exclude escape_path require_symbol
# protected symbol in rule LHS argument
exclude 262_private_in_lhs
# dedukti SR algorithm fails
exclude 273 813
# "sequential"
exclude rule_order 813 1033
# "as"
exclude 729
# "notation"
exclude xor Set quant quant2 Prop prefix parametricCoercions opaque nat_id1 nat_id2 michael max-suc-alg lpparse 861 infix infer indrec implicitArgs3 implicitArgs4 group cr_qu cp0 cp1 cp2 cp3 coercions plus_ac 693 693_assume 679 665 655 655b 649_fo_27 595_and_elim 584_c_slow 579_or_elim_long 579_long_no_duplicate 359 328 245 245b 244 1026 991 706 1101 1190b 1190c 1120 1247 decimal
# "quantifier"
exclude 683 650 573 565 430
# nested module name
exclude require_nondkmident
# module alias
exclude alias
# proofs
exclude why3 tutorial try tautologies rewrite0 rewrite1 rewrite2 rewrite3 rewrite_as_context rewrite_no_capture rewrite_under_binder_no_capture rewrite_under_binders remove natproofs have generalize foo comment_in_qid apply admit change assumption focus assume first_hyp all_hyps 1435_part2 1435
# "open"
exclude triangular power-fact postfix perf_rw_engine perf_rw_fib-nonRightLin perf_rw_nl not-eager nonLeftLinear2 natural Nat lpparse2 logic List FOL Eq doc Bool arity_var arity_diff 922 262_pair_ex_2 215 1141 Tactic 1374 Option String HOL Impred PropExt Classic Comp Pos Z 1217 1151 B1 B2 C1 C2 C3 Epsilon 1313 FunExt Prod Conj Disj ExtraRules Univ 1493
# "inductive"
exclude strictly_positive_1 strictly_positive_2 inductive 989 904 830 341 1392 1407
# underscore in query
exclude unif_hint patterns let 767
# abstracted variable type in rule LHS
exclude 573-2
# domain-free lambda/product
exclude 298_lp 262_parsing tail 698_abst_impl 330 330b 1035 varmatch patt freevars-constraints eta_equality declared boolean abstractions 303 301 292 225 1362 search
# opaque definition with no type (https://github.com/Deducteam/Dedukti/issues/319)
exclude 547
# aborted proof
exclude simp_beta

cd $dir
cat > Makefile <<'__END__'
MAKEFLAGS += -r -k -j$(shell nproc)

SRC := $(shell cat SRC)
LP := $(shell cat FILES)

.PHONY: dko
dko: $(LP:%.lp=%.dko)

%.dko: %.dk
	@echo dk check $< ...
	@dk check -e -q $<

%.dk: $(SRC)/tests/OK/%.lp
	@echo "`basename $<` --> $@ ..."
	@lambdapi export -o raw_dk -v 0 -w $< > $@

include dko.mk

dko.mk: $(LP:%.lp=%.dk)
	@echo generate $@ ...
	@dk dep -q $^ > $@
__END__

TIMEFORMAT="%Es"
time make
