QUIET = --quiet
TESTFILES    = $(wildcard tests/*.dk) $(wildcard examples/*.dk)
OK_TESTFILES = $(wildcard dedukti_tests/OK/*.dk)
KO_TESTFILES = $(wildcard dedukti_tests/KO/*.dk)
SHELL = /bin/bash

all: lambdapi unit_tests tests

lambdapi: lambdapi.ml
	@echo "[OPT] $^ → $@"
	@ocamlfind ocamlopt -pp pa_ocaml -package bindlib,unix,earley,earley.str \
		-linkpkg -o $@ $^

.PHONY: tests
tests: lambdapi
	@echo "## Timing on examples ##"
	@time for file in $(TESTFILES) ; do \
		echo "$$file" ; \
		./lambdapi $(QUIET) $$file ; \
	done
	@echo -n "Number of lines: "
	@wc -l lambdapi.ml | cut -d ' ' -f 1

unit_tests: lambdapi
	@echo "## OK tests ##"
	@for file in $(OK_TESTFILES) ; do \
		echo -n "Testing file \"$$file\" " ; \
		./lambdapi $(QUIET) $$file 2> /dev/null \
		  && echo -e "\033[0;32mOK\033[0m" || echo -e "\033[0;31mKO\033[0m" ; \
	done
	@echo "## KO tests ##"
	@for file in $(KO_TESTFILES) ; do \
		echo -n "$$file " ; \
		./lambdapi $(QUIET) $$file 2> /dev/null \
		  && echo -e "\033[0;31mKO\033[0m" || echo -e "\033[0;32mOK\033[0m" ; \
	done


clean:
	@rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;
	@rm -f lambdapi
