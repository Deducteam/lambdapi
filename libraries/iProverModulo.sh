#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/iProverModulo_dk.tar.gz"
DIR="iProverModulo"

# Cleaning up.
if [ -f ${DIR} ]; then
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
echo "#REQUIRE FOL." > iProverModulo.dk
for sig in `ls *_sig.dk`; do
  base="${sig%%_sig.dk}"
  prf="${base}_prf.dk"
  sed -i "s/^#NAME/#REQUIRE FOL.\n#NAME/g" ${sig}
  sed -i "s/^#NAME/#REQUIRE FOL.\n#REQUIRE ${base}_sig.\n#NAME/g" ${prf}
  echo "#REQUIRE ${base}_sig." >> iProverModulo.dk
  echo "#REQUIRE ${base}_prf." >> iProverModulo.dk
done

echo "DONE."
