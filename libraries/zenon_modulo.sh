#!/bin/bash

NBWORKERS="${NBWORKERS:-1}"

SRC="http://deducteam.gforge.inria.fr/lib/zenon_modulo.tar"
DIR="zenon_modulo"

# Cleaning command (clean and exit).
if [[ "$#" -eq 1 && ("$1" = "clean" || "$1" = "fullclean") ]]; then
  rm -rf ${DIR}
  if [[ "$1" = "fullclean" ]]; then
    rm -f zenon_modulo.tar
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
  if [[ ! -f zenon_modulo.tar ]]; then
    echo -n "  - downloading...           "
    wget -q ${SRC}
    echo "OK"
  fi

  # Extracting the source files.
  echo -n "  - extracting...            "
  tar xf zenon_modulo.tar
  echo "OK"

  # Renaming file.
  echo -n "  - renaming file...         "
  mv ${DIR}/logic/basics_minimal.dk ${DIR}/logic/basics.dk
  echo "OK"

  # All done.
  echo "Ready."
  echo ""
fi

# Cleaning up.
rm -rf ${DIR}/workdir
mkdir -p ${DIR}/workdir

# Preparing the theory files.
echo "preparing logic files... "
for FILE in `ls ${DIR}/logic/*.dk`; do
  MODNAME="$(basename $FILE .dk)"
  OUTFILE="${DIR}/workdir/${MODNAME}.dk"
  ocaml ../misc/deps.ml $FILE $MODNAME > $OUTFILE
  cat $FILE | grep -v "^#NAME" >> $OUTFILE
done

# Moving to the working directory.
cd ${DIR}/workdir

# Compiling the theory files.
echo "Compiling the theory files..."
lambdapi check --verbose 0 --gen-obj --lib-root . --no-warnings *.dk

# Checking function.
function check() {
  # Single file checking function.
  function check_gz() {
    LIBFILE="$1"
    FILE_GZ="$(basename $1)"
    FILE_DK="$(basename $FILE_GZ .gz)"
    MODNAME="${FILE_DK%%.dk}"

    cp ${LIBFILE} ${FILE_GZ}
    gzip -d ${FILE_GZ}
    ocaml ../../../tools/deps.ml ${FILE_DK} ${MODNAME} > ${MODNAME}.aux
    cat ${FILE_DK} | grep -v "^#NAME" >> ${MODNAME}.aux
    mv ${MODNAME}.aux ${FILE_DK}

    lambdapi check --verbose 0 --lib-root . --no-warnings ${FILE_DK}
    if [ $? -ne 0 ]; then
      echo -e "\033[0;31mKO\033[0m ${FILE_GZ}"
      echo "FAILED ${FILE_GZ}" >> error.log
    else
      echo -e "\033[0;32mOK\033[0m ${FILE_GZ}"
    fi
    rm -f ${FILE_DK}
  }

  # Export the single file checking function.
  export -f check_gz

  # Run check on all files.
  echo "Compiling the library files with ${NBWORKERS} processes..."
  find ../files -type f | sort \
    | xargs -P ${NBWORKERS} -n 1 -I{} bash -c "check_gz {}"
}


# Export stuff for the checking function.
export readonly NBWORKERS=${NBWORKERS}
export -f check

# Compiling the library files.
\time -f "Finished in %E at %P with %MKb of RAM" bash -c "check"
