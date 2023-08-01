#!/bin/bash

echo '############ test export -o lp ############'

lambdapi=${lambdapi:-_build/install/default/bin/lambdapi}

TIMEFORMAT="%Es"

rm -rf /tmp/tests
mkdir -p "/tmp/tests/OK/a b"
cp tests/lambdapi.pkg /tmp/tests/

# translate lp files
translate() {
    echo translate lp files ...
    for f in tests/OK/*.lp 'tests/OK/a b/escape file.lp'
    do
        case $f in
            tests/OK/why3*.lp);; #FIXME
            *) out=/tmp/$f
               echo "$f --> $out ..."
               $lambdapi export -o lp -w -v 0 "$f" > "$out"
               if test $? -ne 0; then echo KO; exit 1; fi
        esac
    done
}
time translate

# check lp files
check() {
    echo check lp files ...
    for f in /tmp/tests/OK/*.lp '/tmp/tests/OK/a b/escape file.lp'
    do
        case $f in
            /tmp/tests/OK/why3*.lp);; #FIXME
            *) echo "lambdapi check $f ..."
               $lambdapi check -w -v 0 "$f"
               if test $? -ne 0; then echo KO; exit 1; fi
        esac
    done
}
time check

#cd $root
echo OK
