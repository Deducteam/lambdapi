#!/bin/sh

echo replace dashes by underscores in filenames ...
for f in *.dk
do
    g=`echo $f | sed -e 's/-/_/g'`
    if test "$f" != "$g"
    then
        echo rename $f into $g
        mv $f $g
    fi
done
