all: test

lexer.ml: lexer.mll
	@echo "[LEX] $<"
	@ocamllex -q $<

menhir_parser.ml: menhir_parser.mly lexer.cmx raw.cmx
	@echo "[MHR] $<"
	@menhir --external-tokens Lexer --infer $<

menhir_parser.mli: menhir_parser.ml

raw.cmx: raw.ml
	@echo "[OPT] $<"
	@ocamlopt -c $<

lexer.cmx: lexer.ml
	@echo "[OPT] $<"
	@ocamlopt -c $<

menhir_parser.cmi: menhir_parser.mli lexer.cmx raw.cmx
	@echo "[OPT] $<"
	@ocamlopt -c $<

menhir_parser.cmx: menhir_parser.ml menhir_parser.cmi lexer.cmx raw.cmx
	@echo "[OPT] $<"
	@ocamlopt -c $<

test: raw.cmx lexer.cmx menhir_parser.cmx test.ml
	@echo "[OPT] $<"
	@ocamlopt -o $@ $^

clean:
	@rm -f *~ *.cmx *.cmi *.o

distclean: clean
	@rm -f lexer.ml menhir_parser.ml menhir_parser.mli test
