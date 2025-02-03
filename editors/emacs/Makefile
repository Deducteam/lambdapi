.POSIX:
LAMBDAPI_FILE = lambdapi-mode.el
VERSION = $(shell awk '/^;; Version: /{print $$3;exit}' $(LAMBDAPI_FILE))
NAME = $(shell grep "^(provide" $(LAMBDAPI_FILE) | grep ")" | grep -v "legacy" | sed "s/(provide '\(.*\))/\1/")
# The path to lambdapi built by dune
LAMBDAPI = ../../_build/install/default/bin/lambdapi

EMACS = emacs

SRC =
SRC += lambdapi-abbrev.el
SRC += lambdapi-capf.el
SRC += lambdapi-input.el
SRC += lambdapi-layout.el
SRC += $(LAMBDAPI_FILE)
SRC += lambdapi-mode-pkg.el
SRC += lambdapi-proofs.el
SRC += lambdapi-smie.el
SRC += lambdapi-vars.el

$(NAME)-$(VERSION).tar: $(SRC)
	mkdir -p "$(NAME)-$(VERSION)"
	cp *.el "$(NAME)-$(VERSION)"
	tar -cf "$(NAME)-$(VERSION)".tar "$(NAME)-$(VERSION)"

.PHONY: lambdapi-mode-pkg.el
lambdapi-mode-pkg.el: $(LAMBDAPI_FILE)
	$(eval description := "A major mode for editing Lambdapi source code.")
	$(eval requirements := $(shell grep ";; Package-Requires: " $(LAMBDAPI_FILE) | sed 's/"/\\"/g' | cut -d' ' -f5-))
	@echo "(define-package \"$(NAME)\" \"$(VERSION)\"" > $@
	@echo "  \"$(description)\"" >> $@
	@echo "  '($(requirements))" >> $@

.PHONY: dist
dist: $(NAME)-$(VERSION).tar

.PHONY: check
check: dist
	# This rule depends on the layout of dune. It builds the lambdapi
	# binary so that the "sandboxed" emacs can access it.
	cd ../.. && $(MAKE) lambdapi
	./test.sh "$(NAME)" "$(VERSION)" "$(LAMBDAPI)"

.PHONY: clean
clean:
	rm -f "$(NAME)-$(VERSION)".tar
	rm -rf "$(NAME)-$(VERSION)"
