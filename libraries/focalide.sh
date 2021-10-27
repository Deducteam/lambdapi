#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/focalide.tar.gz"
DIR="focalide"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  if [[ "$1" = "fullclean" ]]; then
    rm -f focalide.tar.gz
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
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
    sed -i "/^#NAME [a-zA-Z_]\+./d" ${FILE}
    sed -i "s/^#SNF/#EVAL/g" ${FILE}
    MODNAME=`basename "${FILE}" ".dk"`
    ocaml ../misc/deps.ml ${FILE} ${MODNAME} > ${FILE}.aux
    cat ${FILE} >> ${FILE}.aux
    mv ${FILE}.aux ${FILE}

    echo "#REQUIRE ${MODNAME}." >> ${DIR}/focalide.dk
  done
  echo "OK"

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm ${DIR}/Makefile
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Checking the files.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" \
  lambdapi check --lib-root . --no-warnings focalide.dk
