#!/bin/sh
#set -e
#set -x

#export PATH=$PWD/_build/install/default/bin:$PATH

# add the exports
mkdir tmp
for i in *.dk; do cat $i | sed "s/^#.*$//g" > tmp/$i; done
touch tmp/cupicef.dk
(cd tmp; for i in *.dk; do ../add_requires.sh $i > $i.imports ; done)

cp cupicef.lp.handmade cupicef.lp

for i in *.dk; do cat header tmp/$i.imports > `basename $i .dk`.lp && lambdapi export -o lp $i >> `basename $i .dk`.lp ; done
lambdapi check -c cupicef.lp
lambdapi check -c Coq__Init__Logic.lp
lambdapi check -c Coq__Init__Datatypes.lp

rm -rf tmp
