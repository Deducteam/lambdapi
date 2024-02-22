#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/holide.tar.gz"
DIR="holide"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  if [[ -d ${DIR} ]]; then find ${DIR} -name '*.lpo' -delete; fi
  if [[ "$1" = "fullclean" ]]; then
    if [[ -d ${DIR} ]]; then find ${DIR} -name '*.dk' -delete; fi
    rm -f holide.tar.gz
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
  if [[ ! -f holide.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC}
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf holide.tar.gz
  echo "OK"

  # Applying the changes (add "#REQUIRE hol" and fix obsolete syntax).
  echo -n "  - applying changes... "
  sed -i "s/^#NAME [a-zA-Z0-9_]\+.//g" "${DIR}/hol.dk"
  for FILE in `find ${DIR} -type f -name "*.dk"`; do
    if [ ${FILE} != "${DIR}/hol.dk" ]; then
      sed -i -e "s/^#NAME [a-zA-Z0-9_]\+./#REQUIRE hol./g" \
          -e 's/^[{]\([a-zA-Z0-9_-]*\)[}]/def \1/g' \
          -e 's/^def thm_/thm thm_/g' ${FILE}
    fi
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

# Check the files.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" \
  lambdapi check --lib-root . --no-warnings *.dk
