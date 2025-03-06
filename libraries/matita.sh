#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/matita.tar.gz"
DIR="matita"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  if [[ -d ${DIR} ]]; then find ${DIR} -name '*.lpo' -delete; fi
  if [[ "$1" = "fullclean" ]]; then
    if [[ -d ${DIR} ]]; then find ${DIR} -name '*.dk' -delete; fi
    rm -f matita.tar.gz
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
  exit -1
fi

# Prepare the library if necessary.
if [[ ! -f ${DIR}/matita.dk ]]; then
  # The directory is not ready, so we need to work.
  echo "Preparing the library:"

  # Download the library if necessary.
  if [[ ! -f matita.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC}
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf matita.tar.gz
  echo "OK"

  # Applying the changes (add "#REQUIRE" and create "matita.dk").
  echo -n "  - applying changes... "
  for FILE in `find ${DIR} -type f -name "*.dk"`; do

    # remove \#NAME commands
    # replace every 0 by z to avoid problems with Bindlib
    # replace injective by injective_
    sed -i -e '/^#NAME [a-zA-Z_]\+./d' -e 's/0/z/g' -e 's/injective/injective_/g' ${FILE}

    # add \#REQUIRE commands
    MODNAME=`basename "${FILE}" ".dk"`
    ocaml ../misc/deps.ml ${FILE} ${MODNAME} > ${FILE}.aux
    cat ${FILE} >> ${FILE}.aux
    mv ${FILE}.aux ${FILE}

    # generate matita.dk
    echo "#REQUIRE ${MODNAME}." >> ${DIR}/matita.dk
  done
  # add missing abstraction domain in cic.dk
  sed -i "s/(x => b x)/(x : Term s1 a => b x)/g" ${DIR}/cic.dk
  # comment the proof of le_fact_10 in matita_arithmetic_factorial
  FILE=${DIR}/matita_arithmetics_factorial
  awk -f matita.awk ${FILE}.dk > ${FILE}.aux
  mv -f ${FILE}.aux ${FILE}.dk 
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
rm -f *.lpo
\time -f "Finished in %E at %P with %MKb of RAM" \
  lambdapi check --lib-root . --no-warnings -c matita.dk
