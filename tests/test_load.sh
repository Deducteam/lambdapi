#!/bin/bash

clean () { rm -f tests/OK/*.lpo; }
#trap clean EXIT
set -e

jobs=32
lambdapi=_build/install/default/bin/lambdapi
log=/tmp/lambdapi.output
TIMEFORMAT="%Es"
mk=/tmp/lpo.mk

for f in why3 perf_rw_engine tutorial escape_path req.file.with.dot
do
    exclude="-a ! -name $f.lp $exclude"
done
FILES=`find tests/OK -maxdepth 1 -name '*.lp' $exclude | xargs`

cat > $mk <<__END__
FILES := $FILES
default: \$(FILES:%.lp=%.lpo)
%.lpo: %.lp
	@echo lambdapi check \$(OPTION) \$<
	@$lambdapi check -w -v 0 \$(OPTION) \$<
__END__
for f in $FILES
do
    s=`awk -f tests/deps.awk $f`;
    if test -n "$s"; then echo ${f}o: $s >> $mk; fi
done

clean

echo "############ compile tests/OK files ############"
OPTION='-c' time make -j$jobs -f $mk

echo "############ load tests/OK files ############"
time make -j$jobs -f $mk
