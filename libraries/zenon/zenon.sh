#!/bin/bash

SRC="https://cloud.lsv.ens-cachan.fr/public.php?service=files&t=4b3d24c59694ededc28bd45cb7e8f10d&download"
LAMBDAPI="../../lambdapi.native"
ARCHIVE="zenon_dk.tar.gz"

# Cleaning up.
echo "Cleaning up..."
rm -f *.dk *.dko

# Download the library if necessary.
if [ ! -f zenon_dk.tar.gz ]; then
  wget -q --show-progress -O zenon_dk.tar.gz ${SRC}
fi

# Building theory files.
echo "Building theory files..."
for file in `ls logic/*.dk`; do
  name="`grep "#NAME " $file | awk -F  " " '{print $2}' `dk"
  modname="${name%%.dk}"
  ocaml tools/deps.ml $file $modname > $name
  cat $file >> $name
done

# Compiling the theory files.
echo "Compiling the theory files..."
$LAMBDAPI --verbose 0 *.dk

echo "DONE."
