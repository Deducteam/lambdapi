#!/bin/bash

set -e

echo '############ test export -o dk ############'

dir=/tmp/export_lp
rm -rf $dir
mkdir -p $dir/OK
cp tests/lambdapi.pkg $dir

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

# requires some prover
exclude why3
# takes too much time to check
exclude perf_rw_engine
# irregular name
exclude file.with.dot req.file.with.dot require_symbol escape_path

cd $dir
cat > Makefile <<'__END__'
MAKEFLAGS += -r -k -j$(shell nproc)

SRC := $(shell cat SRC)
LP := $(shell cat FILES)

.PHONY: lpo
lpo: $(LP:%.lp=OK/%.lpo)

%.lpo: %.lp
	@echo lambdapi check $< ...
	@lambdapi check -c -v 0 -w $<

OK/%.lp: $(SRC)/tests/OK/%.lp
	@echo "`basename $<` --> $@ ..."
	@lambdapi export -o lp -v 0 -w $< > $@

include lpo.mk

lpo.mk: $(LP:%=OK/%)
	@echo generate $@ ...
	@lambdapi depend -v 0 -w > $@
__END__

TIMEFORMAT="%Es"
time make
