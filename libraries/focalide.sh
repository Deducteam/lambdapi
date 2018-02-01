#!/bin/bash

LAMBDAPI="../../lambdapi.native"
SRC="https://deducteam.github.io/data/libraries/focalide.tar.gz"
DIR="focalide"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && "$1" = "clean" ]]; then
  rm -rf ${DIR}
  rm -f focalide.tar.gz
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
    echo "Invalid argument, usage: $0 [clean]"
    exit -1
fi

# Prepare the library if necessary.
if [[ ! -d ${DIR} ]]; then
  # The directory is not ready, so we need to work.
  echo "Preparing the library:"

  # Download the library if necessary.
  if [[ ! -f focalide.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC}
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf focalide.tar.gz
  mv focalide_dks focalide
  echo "OK"

  # Applying the changes (add "#REQUIRE" and create "focalide.dk").
  echo -n "  - applying changes... "
  mv ${DIR}/modulogic.dk ${DIR}/zen.dk
  for FILE in `find ${DIR} -type f -name "*.dk"`; do
    MODNAME=`basename "${FILE}" ".dk"`
    ocaml ../tools/deps.ml ${FILE} ${MODNAME} > ${FILE}.aux
    cat ${FILE} >> ${FILE}.aux
    mv ${FILE}.aux ${FILE}

    echo "#REQUIRE ${MODNAME}." >> ${DIR}/focalide.dk
  done
  echo "OK"

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm focalide.tar.gz
  rm ${DIR}/Makefile
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Checking the files.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" ${LAMBDAPI} focalide.dk
