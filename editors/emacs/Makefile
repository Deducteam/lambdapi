VERSION = 0.1
PKG = lambdapi-mode-$(VERSION).tar
SRC = $(wildcard *.el)

$(PKG): $(SRC)
	tar --create --file $@ --transform 's,^,$(patsubst %.tar,%,$@)/,' $^

.PHONY: dist
dist: $(PKG)

.PHONY: tests
tests:
	cd tests && ./test.sh $(VERSION)

.PHONY: install
install: $(PKG)
	emacs --eval "(package-install-file \"$<\")"
