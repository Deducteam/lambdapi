#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/verine.tar.gz"
DIR="verine"

# Cleaning up.
if [ -f ${DIR} ]; then
  rm -rf ${DIR}
fi

# Download the library if necessary.
if [ ! -f verine.tar.gz ]; then
  wget -q --show-progress ${SRC}
fi

# Extracting.
echo "Extracting..."
tar xf verine.tar.gz
rm ${DIR}/Makefile
cd ${DIR}

# Applying the changes.
echo "Applying changes..."
for file in `ls SEQ*.dk`; do
  sed -i "s/^#NAME/#REQUIRE logic.\n#NAME/g" ${file}
done

# Generating a GNUmakefile.
echo "Generating GNUmakefile..."
cat > GNUmakefile <<\EOF
LAMBDAPI = ../../lambdapi.native --verbose 0
ALL      = $(wildcard *.dk)

all: $(ALL:.dk=.dko)

logic.dko: logic.dk
	$(LAMBDAPI) $<

SEQ%.dko: SEQ%.dk logic.dko
	$(LAMBDAPI) $<

clean:
	rm -f *.dko

distclean: clean
	rm -f *~
EOF

echo "DONE."
