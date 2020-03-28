dist:
	tar --create --file lambdapi-mode.tar *.el

.PHONY: install
install: lambdapi-mode.tar
	emacs --batch --eval '(package-install-file $<)'
