all: lambdapi tests

lambdapi: lambdapi.ml
	@echo "[OPT] $^ → $@"
	@ocamlfind ocamlopt -pp pa_ocaml -package bindlib,earley,earley.str \
		-linkpkg -o $@ $^

tests: lambdapi $(wildcard tests/*.lp) $(wildcard examples/*.lp)
	@./$^ --quiet
	@echo "All good."

clean:
	@rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@rm -f lambdapi
