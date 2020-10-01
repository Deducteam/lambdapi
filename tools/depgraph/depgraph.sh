#!/bin/bash
# shellcheck disable=SC2086

set -eu -o pipefail

# UPPERCASE THE FIRST LETTER OF A WORD
function uppercasefirst ()
{
  word=$1
  first=${word:0:1}
  firstupper=${first^^}
  wordwithoutfirst=${word:1}
  echo "${firstupper}${wordwithoutfirst}"
}

errordirectory="error : non-existing directory"
workingdir=$(pwd)
scriptdir=$(dirname "${BASH_SOURCE[0]}")
lambdapidir=$(cd ${scriptdir}/../.. || { echo $errordirectory ; exit 1; } ; pwd)
graph=graph
graphdot=$workingdir/$graph.dot
graphpng=$workingdir/$graph.png

# CHOOSE THE INTERESTING_MODULES MODULES
concat_modules="$@"
if [ -z "$concat_modules" ] ; then
  interesting_modules=( compile handle infer proof sr tactics typing unif )
else
  interesting_modules=( $@ )
fi

# cd $lambdapidir/src/core
# interesting_modules=( )
# for mlfile in $(ls *.ml) ; do
#   if [ $mlfile != parser.ml ] ; then #remove module with ppx/preprocessor extension
#     mlfilenoml=$(basename ${mlfile} .ml)
#     interesting_modules+=( "$mlfilenoml" )
#   fi
# done

# COLORSCHEME
backgroundcolor="#252525"
paired12=( "#a6cee3" "#1f78b4" "#b2df8a" "#33a02c" "#fb9a99" "#e31a1c" "#fdbf6f" "#ff7f00" "#cab2d6" "#6a3d9a" "#ffff99" "#b15928" )
# brbg11 minus the darkest one
brbg11=( "#8c510a" "#bf812d" "#dfc27d" "#f6e8c3" "#f5f5f5" "#c7eae5" "#80cdc1" "#35978f" "#01665e" "#003c30" ) 
# piyg11 minus the darkest one
piyg11=( "#762a83" "#9970ab" "#c2a5cf" "#e7d4e8" "#f7f7f7" "#d9f0d3" "#a6dba0" "#5aae61" "#1b7837" "#00441b" ) 
colorscheme=( "${paired12[@]}" "${piyg11[@]}" "${brbg11[@]}" "${paired12[@]}" "${piyg11[@]}" "${brbg11[@]}" "${paired12[@]}" "${piyg11[@]}" "${brbg11[@]}" )

# GENERATE THE GRAPH TEXT FILE
rm -f $graphdot 
echo "digraph g {" > $graphdot
echo "graph [bgcolor=\"$backgroundcolor\"];" >> $graphdot

icolor=0
for mldependency in "${interesting_modules[@]}" ; do
  mldependencycolor=${colorscheme[$icolor]}
  mldependencywithupper=$(uppercasefirst $mldependency)
  echo "$mldependencywithupper [style=filled,fillcolor=\"$mldependencycolor\"];" >> $graphdot
  for mlfile in "${interesting_modules[@]}" ; do
    mlfilewithupper=$(uppercasefirst $mlfile)
    if [ $mlfile != $mldependency ] ; then
      cd $lambdapidir || { echo $errordirectory ; exit 1; }
      mlfiledependsonmldependency=$(ocamldep -modules src/core/${mlfile}.ml | grep $mldependencywithupper) || true
      if [ -n "$mlfiledependsonmldependency" ] ; then
        cd $lambdapidir/_build/default || { echo $errordirectory ; exit 1; }
        mldependencyfunctions=$(ocamlc -i -I src/core/.core.objs/byte -open Core src/core/${mldependency}.ml 2>&1 | grep -e "^val" | grep -v "type t =" | awk '{print $2}' ) || true
        cd $lambdapidir || { echo $errordirectory ; exit 1; }
        mldependencyfunctioninmlfile=( )
        for function in ${mldependencyfunctions[*]} ; do
          present=$(grep $mldependencywithupper.$function src/core/$mlfile.ml) || true
          if [ -n "$present" ] ; then
            mldependencyfunctioninmlfile+=( "$function\n" )
          fi
        done
        echo "    $mlfilewithupper -> $mldependencywithupper [color=\"$mldependencycolor\",fillcolor=\"$mldependencycolor\",fontcolor=\"$mldependencycolor\",label="\"${mldependencyfunctioninmlfile[*]}\""];" >> $graphdot
      fi
    fi
  done
  icolor=$((icolor+1))
done
echo "}" >> $graphdot

# GENERATE THE GRAPH
cd $workingdir || { echo $errordirectory ; exit 1; }
dot $graphdot -Tpng -o $graphpng
