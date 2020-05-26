VERSION = 1.0

.PHONY: build
build:
	cask build

.PHONY: dist
dist:
	cask package

.PHONY: test
tests: dist
	./test.sh $(VERSION)

.PHONY: clean
clean:
	cask clean-elc
