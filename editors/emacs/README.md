For instructions on how to install the lambdapi mode for Emacs please see https://lambdapi.readthedocs.io/en/latest/emacs.html.

To install the devellopment version of lambdapi mode for Emacs please run on the current directory, `make dist`. This will generate a `$(NAME)-$(VERSION).tar` file. 
Then, in emacs run `M-x package-install-file RET /PATH/TO/TAR/FILE/$(NAME)-$(VERSION).tar RET`