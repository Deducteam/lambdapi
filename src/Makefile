OCAMLBUILD = ocamlbuild -use-ocamlfind -quiet

#### Compilation #############################################################

.PHONY: default
default: lambdapi.native

lambdapi.native: _build/lambdapi.native

_build/lambdapi.native: $(wildcard *.ml)
	$(OCAMLBUILD) lambdapi.native

.PHONY: clean
clean:
	@ocamlbuild -clean
