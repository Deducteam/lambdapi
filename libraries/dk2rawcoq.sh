#!/bin/sh

echo get back original dk files ...
cp -f ../holide-bak/*.dk .
rm -f coq.v

#../patch-filenames.sh

# patch dk files
echo patch hol.dk ...
# remove require's, rewriting rules, and the definitions of the encoding symbols since they are already defined in sttfa.v
sed -i -e '/^#REQUIRE /d' -e '/^type /d' -e '/^bool /d' -e '/^ind /d' -e '/^arr /d' -e '/^def term /d' -e '/ --> /d' -e '/^def proof /d' -e '/^imp /d' -e '/^forall /d' hol.dk
# require sttfa, qualify encoding symbols, and rename symbols that are Coq keywords
sed -i -e '1i #REQUIRE sttfa.' -e 's/type/sttfa._Set/g' -e 's/bool/sttfa.prop/g' -e 's/arr/sttfa.arr/g' -e 's/term/sttfa.El/g' -e 's/proof/sttfa.Prf/g' -e 's/imp/sttfa.imp/g' -e 's/forall/sttfa.all/g' -e 's/exists/_exists/g' hol.dk

echo rename the symbols of the encoding in all the dk files ...
sed -i -e 's/hol.type/sttfa._Set/g' -e 's/hol.bool/sttfa.prop/g' -e 's/hol.ind/sttfa.ind/g' -e 's/hol.arr/sttfa.arr/g' -e 's/hol.term/sttfa.El/g' -e 's/hol.proof/sttfa.Prf/g' -e 's/hol.imp/sttfa.imp/g' -e 's/hol.forall/sttfa.all/g' -e 's/hol.exists/hol._exists/g' *.dk

# check dk files (optional)
# make -j 7 -f ../dk2coq.mk dko

# translate dk files to v files
cp -f ../sttfa.v .
make LAMBDAPI='lambdapi export -o raw_coq --no-implicits' -j 7 -f ../dk2coq.mk

# post-processing for checking files in Emacs
echo replace \"Require\" by \"From Holide Require\" in all v files ...
sed -i -e 's/^Require /From Holide Require /' *.v

# check generated v files
echo -R . Holide `ls *.v` > _CoqProject
coq_makefile -f _CoqProject -o coq.mk
rm -f *.vo
make -j 7 -f coq.mk
