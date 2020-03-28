dist:
	tar --create --file lambdapi-mode.tar *.tar

.PHONY: install
install: lambdapi-mode.tar
	emacs --batch --eval '(package-install-file $<)'
