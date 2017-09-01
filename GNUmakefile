all: lambdapi

lambdapi: lambdapi.ml
	ocamlfind ocamlopt -pp pa_ocaml \
		-package bindlib,earley,earley.str -linkpkg -o $@ $^

clean:
	rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	rm -f *~ lambdapi
