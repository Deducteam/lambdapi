.POSIX:

VERSION = 1.1.0
NAME = lambdapi

EMACS   = emacs

SRC =
SRC += lambdapi-abbrev.el
SRC += lambdapi-capf.el
SRC += lambdapi-input.el
SRC += lambdapi-layout.el
SRC += lambdapi-mode.el
SRC += lambdapi-pkg.el
SRC += lambdapi-proofs.el
SRC += lambdapi-smie.el
SRC += lambdapi-vars.el

$(NAME)-$(VERSION).tar: $(SRC)
	mkdir -p "$(NAME)-$(VERSION)"
	cp *.el "$(NAME)-$(VERSION)"
	tar --create --file "$(NAME)-$(VERSION)".tar "$(NAME)-$(VERSION)"
	rm -r "$(NAME)-$(VERSION)"

.PHONY: install
install: $(NAME)-$(VERSION).tar
	@echo "To install the mode in emacs, use"
	@echo "> M-x package-install-file RET $(NAME)-$(VERSION).tar RET"

.PHONY: dist
dist: $(NAME)-$(VERSION).tar

.PHONY: check
check: dist
	./test.sh $(VERSION)

.PHONY: clean
clean:
	rm -rf "$(NAME)-$(VERSION)"
	rm -f "$(NAME)-$(VERSION)".tar
