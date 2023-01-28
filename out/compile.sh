#!/bin/sh
#set -e
#set -x

#export PATH=$PWD/_build/install/default/bin:$PATH

for i in *.dk.gz; do rm -f `basename $i .gz`; gunzip -k $i; done
touch cupicef.dk

for i in *.dk; do
  LPFILE=`basename $i .dk`.lp
  # add the flags
  cat header > $LPFILE
  # add the exports
  ./add_requires.sh $i >> $LPFILE
  lambdapi export -o lp $i >> $LPFILE ;
done
cp cupicef.lp.handmade cupicef.lp

rm *.dk

lambdapi check -c Coq__Init__Peano.lp
