lambdapi-mode-0.1.tar:
	mkdir lambdapi-mode-0.1
	cp *.el lambdapi-mode-0.1
	tar --create --file $@ lambdapi-mode-0.1
	$(RM) -rf lambdapi-mode-0.1

.PHONY: dist
dist: lambdapi-mode-0.1.tar

.PHONY: install
install: lambdapi-mode-0.1.tar
	emacs --eval "(package-install-file \"$<\")"
