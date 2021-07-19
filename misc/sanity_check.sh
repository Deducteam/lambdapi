#!/bin/sh
set -eu

files=`find src -name \*.ml -o -name \*.ml[iy]`

# Check for long lines.
gawk '/@see/{next}length>78    {print "In " FILENAME ", line " FNR " more than 78 characters..."}' $files

# Check for trailing spaces.
gawk '/.*\s$/      {print "In " FILENAME ", line " FNR " has trailing spaces..."}' $files

# Check for tabulations.
gawk '/.*\t.*/     {print "In " FILENAME ", line " FNR " contains tabulations..."}' `echo $files | sed -e 's|src/cli/init.ml||'`

# Check for [Pervasives].
gawk '/Pervasives/ {print "In " FILENAME ", line " FNR " use of [Pervasives] should be replaced by [Stdlib]..."}' $files
