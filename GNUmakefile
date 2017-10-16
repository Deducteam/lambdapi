QUIET = --quiet
TESTFILES = $(wildcard tests/*.lp) $(wildcard examples/*.lp)

all: lambdapi tests

lambdapi: lambdapi.ml
	@echo "[OPT] $^ → $@"
	@ocamlfind ocamlopt -pp pa_ocaml -package bindlib,unix,earley,earley.str \
		-linkpkg -o $@ $^

.PHONY: tests
tests: lambdapi
	@echo -n "Number of lines: "
	@wc -l lambdapi.ml | cut -d ' ' -f 1
	@time for file in $(TESTFILES) ; do \
		echo "Testing file \"$$file\"" ; \
		./lambdapi $(QUIET) $$file ; \
	done;

clean:
	@rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.lpo" -exec rm {} \;
	@rm -f lambdapi
