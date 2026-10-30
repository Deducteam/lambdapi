#!/bin/bash

set -e

out=/tmp/lambdapi.output
TIMEFORMAT="%Es"

IFS='/' read -ra ADDR <<< "$1"
repo_path="${ADDR[-1]}"
IFS='.' read -ra ADDR <<< "$repo_path"
repo_path="/tmp/${ADDR[0]}"

if [ -d "$repo_path" ] ; then
    rm -fr "$repo_path"
fi
git clone $1 $repo_path

cd $repo_path
time make
