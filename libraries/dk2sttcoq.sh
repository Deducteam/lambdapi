#!/bin/sh

echo get back original dk files ...
cp -f ../holide-bak/*.dk .
rm -f sttfa.v

#../patch-filenames.sh

# patch dk files
echo qualify encoding symbols in hol.dk ...
# symbols defined in hol.dk
for n in `awk '/^def /{print$2;next}/^[a-zA-Z0-9_]+ /{print$1}' hol.dk`
do
    sed -i -e "s/ $n / hol.$n /g" -e "s/ $n\./ hol.$n./g" -e "s/($n /(hol.$n /g" -e "s/ $n)/ hol.$n)/g" -e "s/ $n$/ hol.$n/g" hol.dk
done
sed -i -e 's/^hol.//' -e 's/def hol./def /' -e 's/thm hol./thm /' hol.dk

# because "type" is not accepted in mapping.lp
echo replace \"hol.type\" by \"hol.typ\" in all dk files ...
sed -i -e 's/^type /typ /' hol.dk
sed -i -e 's/hol.type/hol.typ/g' *.dk

# check dk files (optional)
# make -j 7 -f ../dk2coq.mk dko

# translate dk files to v files
cp ../coq.v .
make -j 7 -f ../dk2coq.mk

# post-processing for checking files in Emacs
echo replace \"Require\" by \"From Holide Require\" in all v files ...
sed -i -e 's/^Require /From Holide Require /' *.v

# check generated v files
echo -R . Holide `ls *.v` > _CoqProject
coq_makefile -f _CoqProject -o coq.mk
rm -f *.vo
make -j 7 -f coq.mk
