OCAMLBUILD   = ocamlbuild -use-ocamlfind -quiet
TESTFILES    = $(wildcard tests/*.dk) \
							 $(wildcard examples/*.dk) \
							 $(wildcard other_examples/*.dk) \
							 $(wildcard dedukti_tests/OK/*.dk)
OK_TESTFILES = $(wildcard dedukti_tests/OK/*.dk)
KO_TESTFILES = $(wildcard dedukti_tests/KO/*.dk)
TIME         = /usr/bin/time -f "%E at %P with %MKb of RAM"

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
	@for file in $(TESTFILES) ; do \
		echo "$$file" ; \
		./lambdapi.native --verbose 0 $$file ; \
	done

.PHONY: matita
matita: lambdapi.native $(wildcard libraries/matita/*.dk)
	@echo "## Compiling the Matita's arithmetic library ##"
	@cd libraries && ./matita.sh

.PHONY: focalide
focalide: lambdapi.native $(wildcard libraries/focalide/*.dk)
	@echo "## Compiling focalide library ##"
	@cd libraries/focalide && $(TIME) ../../lambdapi.native focalide.dk

.PHONY: holide
ifneq ("$(wildcard libraries/holide)","")
holide: lambdapi.native $(wildcard libraries/holide/*.dk)
	@echo "## Compiling holide library ##"
	@$(TIME) make -C libraries/holide
else
holide:
	@echo "You must first run 'cd libraries; ./holide.sh; cd ..'"
endif

.PHONY: verine
ifneq ("$(wildcard libraries/verine)","")
verine: lambdapi.native $(wildcard libraries/verine/*.dk)
	@echo "## Compiling verine library ##"
	@$(TIME) make -C libraries/verine
else
verine:
	@echo "You must first run 'cd libraries; ./verine.sh; cd ..'"
endif

.PHONY: iProverModulo
ifneq ("$(wildcard libraries/iProverModulo)","")
iProverModulo: lambdapi.native $(wildcard libraries/iProverModulo/*.dk)
	@echo "## Compiling iProverModulo library ##"
	@$(TIME) make -C libraries/iProverModulo
else
iProverModulo:
	@echo "You must first run 'cd libraries; ./iProverModulo.sh; cd ..'"
endif

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

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;
	@rm -f lambdapi.native
	@cd libraries && ./matita.sh clean

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
