AWK ?= awk
SRC = rec_hs_to_lp.awk

.PHONY: tests
tests:
	$(AWK) -f $(SRC) tests/ex.hs

.PHONY: clean
clean:
	$(RM) -r DEDUKTI/ HASKELL/ CAFEOBJ-B/ MAUDE/ OCAML/
