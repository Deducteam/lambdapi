#!/bin/bash

set -e

dir=/tmp/test_load
rm -rf $dir
mkdir -p $dir/tests/OK

cp tests/OK/*.lp $dir/tests/OK
cp resources/Makefile tests/lambdapi.pkg $dir/tests

# excluded files
cd $dir/tests/OK
rm -f why3.lp # because it requires why3
rm -f perf_rw_engine.lp # because it takes too long
rm -f escape_path.lp req.file.with.dot.lp require_symbol.lp # because of irregular names

cd $dir/tests
cat >> Makefile <<'__END__'
.PHONY: load
load: $(LPO:%.lpo=%.load)

%.load: %.lpo
	@echo lambdapi load $< ...
	@lambdapi check -v 0 -w $<
__END__

echo "############ compile tests/OK files ############"
time make LP_OPTIONS='-c -v 0 -w'

echo "############ load tests/OK files ############"
time make load LP_OPTIONS='-c -v 0 -w'
