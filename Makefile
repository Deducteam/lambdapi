VIMDIR = $(HOME)/.vim
EMACS  = $(shell which emacs)

#### Compilation (binary, library and documentation) #########################

.PHONY: default
default: lambdapi

.PHONY: lambdapi
lambdapi:
	@dune build --only-packages lambdapi @install

.PHONY: odoc
odoc:
	@dune build --only-packages lambdapi @doc

.PHONY: doc
doc: bnf
	$(MAKE) -C doc html

.PHONY: bnf
bnf:
	$(MAKE) -C doc -f Makefile.bnf

#### Unit tests and sanity check #############################################

.PHONY: tests
tests: lambdapi
	@dune runtest
	@dune exec --only-packages lambdapi -- tests/runtests.sh
	@dune exec --only-packages lambdapi -- tests/dtrees.sh
	@dune exec --only-packages lambdapi -- tests/export_dk.sh
	@dune exec --only-packages lambdapi -- tests/export_lp.sh

.PHONY: tests_alt_ergo
tests_alt_ergo: lambdapi
	@dune exec --only-packages lambdapi -- lambdapi check tests/OK/why3*.lp

.PHONY: sanity_check
sanity_check: misc/sanity_check.sh
	@./$<

#### Library tests ###########################################################

.PHONY: matita
matita: lambdapi
	@printf "## Compiling the Matita's arithmetic library ##\n"
	@cd libraries && dune exec -- ./matita.sh

.PHONY: focalide
focalide: lambdapi
	@printf "## Compiling focalide library ##\n"
	@cd libraries && dune exec -- ./focalide.sh

.PHONY: holide
holide: lambdapi
	@printf "## Compiling holide library ##\n"
	@cd libraries && dune exec -- ./holide.sh

.PHONY: verine
verine: lambdapi
	@printf "## Compiling verine library ##\n"
	@cd libraries && dune exec -- ./verine.sh

.PHONY: iprover
iprover: lambdapi
	@printf "## Compiling iProverModulo library ##\n"
	@cd libraries && dune exec -- ./iprover.sh

.PHONY: dklib
dklib: lambdapi
	@printf "## Compiling the dklib library ##\n"
	@cd libraries && dune exec -- ./dklib.sh

.PHONY: zenon_modulo
zenon_modulo: lambdapi
	@printf "## Compiling the zenon library ##\n"
	@cd libraries && dune exec -- ./zenon_modulo.sh

#### Cleaning targets ########################################################

.PHONY: lpoclean
lpoclean:
	@find . -type f -name "*.lpo" -exec rm {} \;

.PHONY: clean
clean: lpoclean
	@dune clean
	@$(MAKE) -C editors/emacs clean
	@$(MAKE) -C editors/vscode clean

.PHONY: distclean
distclean: clean
	@cd libraries && ./matita.sh clean
	@cd libraries && ./focalide.sh clean
	@cd libraries && ./holide.sh clean
	@cd libraries && ./verine.sh clean
	@cd libraries && ./iprover.sh clean
	@cd libraries && ./dklib.sh clean
	@cd libraries && ./zenon_modulo.sh clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.gv" -exec rm {} \;

.PHONY: fullclean
fullclean: distclean
	@cd libraries && ./matita.sh fullclean
	@cd libraries && ./focalide.sh fullclean
	@cd libraries && ./holide.sh fullclean
	@cd libraries && ./verine.sh fullclean
	@cd libraries && ./iprover.sh fullclean
	@cd libraries && ./dklib.sh fullclean
	@cd libraries && ./zenon_modulo.sh fullclean

#### Installation and release targets ########################################

.PHONY: install
install: install_lambdapi

.PHONY: uninstall
uninstall: uninstall_lambdapi

.PHONY: install_lambdapi
install_lambdapi: lambdapi
	@dune install lambdapi

.PHONY: uninstall_lambdapi
uninstall:
	@dune uninstall lambdapi

.PHONY: emacs_mode
emacs_mode:
	@dune build --only-packages emacs_mode @install

.PHONY: install_emacs_mode
install_emacs_mode: emacs_mode
ifeq ($(EMACS),)
	@printf "\e[36mNo 'emacs' binary available in path and EMACS variable \
is not set, \nEmacs mode won't be installed.\e[39m\n"
else
	@dune install emacs_mode
	@printf "\e[36mEmacs mode installed.\e[39m\n"
endif

.PHONY: uninstall_emacs_mode
uninstall_emacs_mode:
	@dune uninstall emacs_mode

.PHONY: install_vim_mode
install_vim_mode: $(wildcard editors/vim/*/*.vim)
ifeq ($(wildcard $(VIMDIR)/.),)
	@printf "\e[36mWill not install vim mode.\e[39m\n"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/dedukti.vim    $(VIMDIR)/syntax
	install -m 644 editors/vim/syntax/lambdapi.vim   $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/dedukti.vim  $(VIMDIR)/ftdetect
	install -m 644 editors/vim/ftdetect/lambdapi.vim $(VIMDIR)/ftdetect
	@printf "\e[36mVim mode installed.\e[39m\n"
endif

.PHONY: uninstall_vim_mode
uninstall_vim_mode:
	rm -f $(VIMDIR)/syntax/dedukti.vim
	rm -f $(VIMDIR)/syntax/lambdapi.vim
	rm -f $(VIMDIR)/ftdetect/dedukti.vim
	rm -f $(VIMDIR)/ftdetect/lambdapi.vim

.PHONY: build-vscode-extension
build-vscode-extension:
	cd editors/vscode && make
	
