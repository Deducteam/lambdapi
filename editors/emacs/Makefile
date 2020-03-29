VERSION = 0.1
PKG = lambdapi-mode-$(VERSION).tar

$(PKG): $(wildcard *.el)
	mkdir lambdapi-mode-$(VERSION)
	cp *.el lambdapi-mode-$(VERSION)
	tar --create --file $@ lambdapi-mode-$(VERSION)
	$(RM) -rf lambdapi-mode-$(VERSION)

.PHONY: dist
dist: $(PKG)

.PHONY: tests
tests:
	cd tests && ./test.sh $(VERSION)

.PHONY: install
install: $(PKG)
	emacs --eval "(package-install-file \"$<\")"
