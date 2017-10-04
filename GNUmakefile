all: lambdapi

lambdapi: lambdapi.ml
	ocamlfind ocamlopt -pp pa_ocaml \
		-package bindlib,earley,earley.str -linkpkg -o $@ $^

test: lambdapi test.lp $(wildcard examples/*.lp)
	@./$^ --quiet
	@echo "OK."

clean:
	rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	find . -type f -name "*~" -exec rm {} \;
	rm -f lambdapi
