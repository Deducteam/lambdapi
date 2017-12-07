OCAMLBUILD   = ocamlbuild -use-ocamlfind -quiet
TESTFILES    = $(wildcard tests/*.dk) \
							 $(wildcard examples/*.dk) \
							 $(wildcard other_examples/*.dk) \
							 $(wildcard dedukti_tests/OK/*.dk)
OK_TESTFILES = $(wildcard dedukti_tests/OK/*.dk)
KO_TESTFILES = $(wildcard dedukti_tests/KO/*.dk)
SHELL = /bin/bash

all: lambdapi.native unit_tests

lambdapi.native: $(wildcard *.ml)
	@echo "[OPT] $@"
	@$(OCAMLBUILD) $@
	@echo -n "Number of lines:"
	@wc -l *.ml | tail -n 1

.PHONY: tests
tests: lambdapi.native
	@echo "## Timing on examples ##"
	@rm -f $(TESTFILES:.dk=.dko)
	@time for file in $(TESTFILES) ; do \
		echo "$$file" ; \
		./lambdapi.native --verbose 0 $$file ; \
	done

.PHONY: matita
matita: lambdapi.native $(wildcard libraries/matita/*.dk)
	@echo "## Compiling matita library ##"
	@cd libraries/matita && time ../../lambdapi.native matita.dk

unit_tests: lambdapi.native
	@echo "## OK tests ##"
	@rm -f $(OK_TESTFILES:.dk=.dko)
	@for file in $(OK_TESTFILES) ; do \
		echo -n "Testing file \"$$file\" " ; \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;32mOK\033[0m" || echo -e "\033[0;31mKO\033[0m" ; \
	done
	@echo "## KO tests ##"
	@rm -f $(KO_TESTFILES:.dk=.dko)
	@for file in $(KO_TESTFILES) ; do \
		echo -n "$$file " ; \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;31mOK\033[0m" || echo -e "\033[0;32mKO\033[0m" ; \
	done

clean:
	@ocamlbuild -clean
	@rm -f *.cmi *.cmo *.cmx *.o

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;
	@rm -f lambdapi.native

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
VIMDIR = $(HOME)/.vim
install_vim: editors/vim/ftdetect/dedukti.vim editors/vim/syntax/dedukti.vim
ifeq ($(wildcard $(VIMDIR)/.),)
	@echo -e "\e[36mWill not install vim mode.\e[39m"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/dedukti.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/dedukti.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
endif
