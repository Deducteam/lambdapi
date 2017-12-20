#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/holide.tar.gz"
DIR="holide"

# Cleaning up.
if [ -d ${DIR} ]; then
  echo "Cleaning up..."
  rm -rf ${DIR}
fi

# Download the library if necessary.
if [ ! -f holide.tar.gz ]; then
  wget -q --show-progress ${SRC}
fi

# Extracting.
echo "Extracting..."
tar xf holide.tar.gz
rm ${DIR}/Makefile
cd ${DIR}

# Applying the changes.
echo "Applying changes..."
for file in `ls *.dk`; do
  if [ ${file} != hol.dk ]; then
    sed -i "s/^#NAME/#REQUIRE hol.\n#NAME/g" ${file}
    sed -i 's/^[{]\([a-zA-Z0-9_-]*\)[}]/def \1/g' ${file}
  fi
done

# Generating a GNUmakefile.
echo "Generating GNUmakefile..."
cat > GNUmakefile <<\EOF
LAMBDAPI = ../../lambdapi.native --verbose 0
ALL      = $(wildcard *.dk)

all: $(ALL:.dk=.dko)

hol.dko: hol.dk
	$(LAMBDAPI) $<

%.dko: %.dk hol.dko
	$(LAMBDAPI) $<

clean:
	rm -f *.dko

distclean: clean
	rm -f *~
EOF

echo "DONE."
