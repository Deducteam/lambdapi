#!/bin/bash

set -e

dune build

clean () { rm -f tests/OK/*.lpo; }
trap clean ERR

lambdapi='_build/install/default/bin/lambdapi'
mk=/tmp/lpo.mk
jobs=$(nproc)
TIMEFORMAT="%Es"

# excluded test files
for f in why3 perf_rw_engine tutorial escape_path req.file.with.dot
do
    exclude="-a ! -name $f.lp $exclude"
done
FILES=`find tests/OK -maxdepth 1 -name '*.lp' $exclude | xargs`

# generate Makefile $mk
cat > $mk <<__END__
LAMBDAPI := $lambdapi check -w -v 0
FILES := $FILES
lpo: \$(FILES:%.lp=%.lpo)
%.lpo: %.lp
	@echo generate \$*.lpo ...
	@\$(LAMBDAPI) -c \$*.lp
load: \$(FILES:%.lp=%.load)
%.load: %.lp
	@echo load \$*.lpo ...
	@\$(LAMBDAPI) \$*.lp
__END__

# add file dependencies
for f in $FILES
do
    s=`awk -f tests/deps.awk $f`;
    if test -n "$s"; then echo ${f}o: $s >> $mk; fi
done

# remove lpo files
clean

echo "############ compile tests/OK files ############"
time make -j$jobs -f $mk lpo

echo "############ load tests/OK files ############"
time make -j$jobs -f $mk load
