#!/bin/bash

SRC="https://deducteam.github.io/data/libraries/verine.tar.gz"
DIR="verine"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  if [[ "$1" = "fullclean" ]]; then
    rm -f verine.tar.gz
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
  if [[ ! -f verine.tar.gz ]]; then
    echo -n "  - downloading...      "
    wget -q ${SRC}
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...       "
  tar xf verine.tar.gz
  echo "OK"

  # Applying the changes (add "#REQUIRE logic", remove "#NAME ...").
  echo -n "  - applying changes... "

  # remove SEQ005_size7.dk which takes too much memory
  rm -f ${DIR}/SEQ005_size7.dk

  # remove \#NAME commands
  # replace every 0 by z because 0 is not a valid id
  sed -i -e '/^#NAME [a-zA-Z0-9_]\+./d' -e 's/0/z/g' ${DIR}/logic.dk
  for FILE in `ls ${DIR}/SEQ*.dk`; do
    sed -i -e 's/^#NAME [a-zA-Z0-9_]\+./#REQUIRE logic./' -e 's/0/z/g' ${FILE}
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

# Checking function.
function check_verine() {
  LP='lambdapi check --lib-root . --no-warnings'
  rm -f logic.lpo
  ${LP} -c logic.dk
  for FILE in `ls SEQ*.dk`; do ${LP} ${FILE}; done
}

# Export the checking function.
export -f check_verine

# Run the actual checks.
cd ${DIR}
\time -f "Finished in %E at %P with %MKb of RAM" bash -c "check_verine"
