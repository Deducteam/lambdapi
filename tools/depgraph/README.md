This is a temporary shell script generating the ocaml dependency graph.

-- How it works ?

1. it gets the dependencies with ``ocamldep ... | grep ...``
2. it generates the \*.mli from the \*.ml and gets the constants and functions with ``ocamlc.opt -i ... | grep -e "^val"`` 
3. it gets the constants and functions in the dependency by greping the sources
4. it generates the dot files with one colour by module dependency

-- How to use it ?

1. choose a set of interesting modules : change the interesting_modules variable
2. remove the interesting ``open Module`` in sources so that functions are explicitly called by ``Module.function a b c``. If you don't do it, you will get the graph with the modules (the nodes) and their dependencies (the edges) but you will miss the called functions (label on the edges)
3. the script has to be used after building lambdapi with dune (as it uses the the src/core/.core.objs/byte/\*.cmi files)
4. just call the script : ``./depgraph.sh``

-- Why it sucks ?

1. it's really a build-system (dune) job to generate such things
2. it should be written in ocaml (and using the graphviz library)
3. it doesn't work correctly with submodules
4. it's grep-ing the source instead of using the compiler libs to get the list of defined symbols
