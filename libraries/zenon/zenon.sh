#!/bin/bash

NBWORKERS="4"
SRC="https://cloud.lsv.ens-cachan.fr/public.php?service=files&t=8f8231877f5034cd8c27c53b085bd9d6&download"
LAMBDAPI="../../lambdapi.native"
ARCHIVE="zenon.tar"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -f *.dk *.dko *.aux error.log
  rm -rf zenon_dk
  rm -f zenon_dk.tar.gz
  if [[ "$1" = "fullclean" ]]; then
    rm -f zenon.tar
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
  exit -1
fi

# Cleaning up.
echo "Cleaning up..."
rm -f *.dk *.dko

# Download the archive if necessary.
if [ ! -f ${ARCHIVE} ]; then
  if [ ! -f zenon_dk.tar.gz ]; then
    echo "Downloading the archive..."
    wget -q --show-progress -O zenon_dk.tar.gz ${SRC}
  fi
  echo "Extracting..."
  tar xf zenon_dk.tar.gz
  echo "Creating the new archive using ${NBWORKERS} processes..."
  cd zenon_dk
  rm zenon_focal.dk
  ls *.dk | xargs -P ${NBWORKERS} -n 1 gzip
  tar cf zenon.tar *.dk.gz
  cd ..
  mv zenon_dk/zenon.tar .
  echo "Cleaning up archives..."
  rm -rf zenon_dk zenon_dk.tar.gz
fi

# Building theory files.
echo "Building theory files..."
for file in `ls logic/*.dk`; do
  name="`grep "#NAME " $file | awk -F  " " '{print $2}' `dk"
  modname="${name%%.dk}"
  ocaml ../../tools/deps.ml $file $modname > $name
  cat $file >> $name
done

# Compiling the theory files.
echo "Compiling the theory files..."
$LAMBDAPI --verbose 0 --gen-obj *.dk

# Compilation function.
export readonly GARCHIVE=${ARCHIVE}
export readonly GLAMBDAPI=${LAMBDAPI}

function test_gz() {
  file_gz="$1"
  file_dk=${file_gz%%.gz}
  modname=${file_dk%%.dk}
  tar xf ${GARCHIVE} $file_gz
  gzip -d $file_gz
  ocaml ../../tools/deps.ml $file_dk $modname > $modname.aux
  cat $file_dk >> $modname.aux
  mv $modname.aux $file_dk
  ${GLAMBDAPI} --verbose 0 $file_dk
  if [ $? -ne 0 ]; then
    echo -e "$modname \033[0;31mKO\033[0m"
    echo "FAILED $file_gz" >> error.log
  else
    echo -e "$modname \033[0;32mOK\033[0m"
  fi
  rm -f $file_dk $modname.dko
}

export -f test_gz

# Compiling the library files.
echo "Compiling the library files with ${NBWORKERS} processes..."
tar -tf ${ARCHIVE} | xargs -P ${NBWORKERS} -n 1 -I{} bash -c "test_gz {}"

echo "DONE."
