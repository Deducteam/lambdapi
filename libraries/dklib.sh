#!/bin/bash

SRC="https://github.com/rafoo/dklib/archive/v2.6.zip"
DIR="dklib"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  rm -rf dklib-2.6
  if [[ "$1" = "fullclean" ]]; then
    rm -f dklib.zip
  fi
  exit 0
fi

# Rejecting other command line arguments.
if [[ "$#" -ne 0 ]]; then
  echo "Invalid argument, usage: $0 [clean | fullclean]"
  exit -1
fi

# Checking for the "lambadpi" command (first in LAMBDAPI).
if [[ ! -v LAMBDAPI ]]; then
  # Falling back to installed "lambdapi" command.
  LAMBDAPI="$(which lambdapi 2> /dev/null)"
  if [[ -z "${LAMBDAPI}" ]]; then
    echo "No lambdapi command found... (not in path)"
    echo "A command may be specified with the LAMBDAPI environment variable."
    exit -1
  fi
fi

# Prepare the library if necessary.
if [[ ! -d ${DIR} ]]; then
  # The directory is not ready, so we need to work.
  echo "Preparing the library:"

  # Download the library if necessary.
  if [[ ! -f dklib.zip ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC} -O dklib.zip
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  unzip -qq dklib.zip
  mv dklib-2.6 ${DIR}
  echo "OK"

  # Applying the changes (create "dklib.dk").
  echo -n "  - applying changes... "
  for FILE in `find ${DIR} -type f -name "*.dk"`; do
    MODNAME=`basename "${FILE}" ".dk"`

    if [[ "${MODNAME}" = "dk_monads_coc" ]]; then
      echo "(;#REQUIRE ${MODNAME}.;)" >> ${DIR}/dklib.dk
    else
      echo "#REQUIRE ${MODNAME}." >> ${DIR}/dklib.dk
    fi
  done
  echo "OK"

  # Cleaning up.
  echo -n "  - cleaning up...      "
  rm ${DIR}/Makefile ${DIR}/.gitignore ${DIR}/README.org
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Checking the files.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" \
  ${LAMBDAPI} --lib-root . --no-warnings dklib.dk
