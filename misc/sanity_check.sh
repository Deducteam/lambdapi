#!/bin/sh
set -eu

files=`find src -name \*.ml -o -name \*.ml[iy]`
out=/tmp/sanity_check.log

rm -f $out
touch $out

# Check for long lines.
gawk '/@see/{next}length>78    {print "In " FILENAME ", line " FNR " more than 78 characters..."}' $files >> $out

# Check for trailing spaces.
gawk '/.*\s$/      {print "In " FILENAME ", line " FNR " has trailing spaces..."}' $files >> $out

# Check for tabulations.
gawk '/.*\t.*/     {print "In " FILENAME ", line " FNR " contains tabulations..."}' `echo $files | sed -e 's|src/cli/init.ml||' -e 's|src/cli/main.ml||'` >> $out

# Check for [Pervasives].
gawk '/Pervasives/ {print "In " FILENAME ", line " FNR " use of [Pervasives] should be replaced by [Stdlib]..."}' $files >> $out

cat $out

if test -s $out; then exit 1; fi
