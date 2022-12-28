#!/bin/sh

echo rename files with dashes ...
for f in *.dk
do
    g=`echo $f | sed -e 's/-/_/g'`
    if test "$f" != "$g"
    then
        echo rename $f into $g
        mv $f $g
    fi
done

echo patch hol.dk ...
sed -i -e '/^#REQUIRE /d' -e '/^type /d' -e '/^bool /d' -e '/^ind /d' -e '/^arr /d' -e '/^def term /d' -e '/ --> /d' -e '/^def proof /d' -e '/^imp /d' -e '/^forall /d' hol.dk
sed -i -e '1i #REQUIRE STTfa.' -e 's/type/STTfa.Set/g' -e 's/bool/STTfa.prop/g' -e 's/arr/STTfa.arr/g' -e 's/term/STTfa.El/g' -e 's/proof/STTfa.Prf/g' -e 's/imp/STTfa.imp/g' -e 's/forall/STTfa.all/g' hol.dk
sed -i -e 's/STTfa.STTfa/STTfa/g' hol.dk

echo rename the symbols of the encoding in all the dk files ...
sed -i -e 's/hol.type/STTfa.Set/g' -e 's/hol.bool/STTfa.prop/g' -e 's/hol.ind/STTfa.ind/g' -e 's/hol.arr/STTfa.arr/g' -e 's/hol.term/STTfa.El/g' -e 's/hol.proof/STTfa.Prf/g' -e 's/hol.imp/STTfa.imp/g' -e 's/hol.forall/STTfa.all/g' *.dk
