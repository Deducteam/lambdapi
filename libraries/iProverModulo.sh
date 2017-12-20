#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/iProverModulo_dk.tar.gz"
DIR="iProverModulo"

# Cleaning up.
if [ -d ${DIR} ]; then
  rm -rf ${DIR}
fi

# Download the library if necessary.
if [ ! -f iProverModulo_dk.tar.gz ]; then
  wget -q --show-progress ${SRC}
fi

# Extracting.
echo "Extracting..."
tar xf iProverModulo_dk.tar.gz
mv iProverModulo_dk ${DIR}
rm ${DIR}/Makefile
cd ${DIR}

# Applying the changes.
echo "Applying changes..."
for sig in `ls *_sig.dk`; do
  base="${sig%%_sig.dk}"
  prf="${base}_prf.dk"
  sed -i "s/^#NAME/#REQUIRE FOL.\n#NAME/g" ${sig}
  sed -i "s/^#NAME/#REQUIRE FOL.\n#REQUIRE ${base}_sig.\n#NAME/g" ${prf}
done

# Generating a GNUmakefile.
echo "Generating GNUmakefile..."
cat > GNUmakefile <<\EOF
LAMBDAPI = ../../lambdapi.native --verbose 0
ALL      = $(wildcard *.dk)

all: $(ALL:.dk=.dko)

FOL.dko: FOL.dk
	$(LAMBDAPI) $<

%_sig.dko: %_sig.dk FOL.dko
	$(LAMBDAPI) $<

%_prf.dko: %_prf.dk %_sig.dko FOL.dko
	$(LAMBDAPI) $<

clean:
	rm -f *.dko

distclean: clean
	rm -f *~
EOF

echo "DONE."
