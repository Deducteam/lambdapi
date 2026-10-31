#!/bin/bash

set -e

echo '############ test export -o dk ############'

dir=/tmp/export_dk
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
# requires some prover
exclude why3
# takes too much time to check
exclude perf_rw_engine
# commutative and non associative symbol
exclude ac
# protected symbol in rule LHS arguments
exclude 262_private_in_lhs
# dedukti SR algorithm fails
exclude 273 813 Conj Disj
# require escaped module name
exclude escape_path require_nondkmident 262_pair_ex_2 require_symbol
# use builtin strings
exclude Tactic
# requires Tactic
exclude 1374 assume first_hyp all_hyps 1493 rewrite_under_binder_no_capture

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
	@lambdapi export -o dk -v 0 -w $< > $@

include dko.mk

dko.mk: $(LP:%.lp=%.dk)
	@echo generate $@ ...
	@dk dep -q $^ > $@
__END__

TIMEFORMAT="%Es"
time make
