# Minimal makefile for Sphinx documentation
#

# You can set these variables from the command line.
SPHINXOPTS    =
SPHINXBUILD   = sphinx-build
SOURCEDIR     = .
BUILDDIR      = _build
BNF_GEN       = obelisk

# Put it first so that "make" without argument is like "make help".
help:
	@$(SPHINXBUILD) -M help "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

.PHONY: help Makefile

# Catch-all target: route all unknown targets to Sphinx using the new
# "make mode" option.  $(O) is meant as a shortcut for $(SPHINXOPTS).
%: Makefile
	@$(SPHINXBUILD) -M $@ "$(SOURCEDIR)" "$(BUILDDIR)" $(SPHINXOPTS) $(O)

syntax.bnf:
	$(BNF_GEN) ../src/core/lpParser.mly | \
sed 's/WILD/"_"/g' | \
sed 's/L_PAREN/"("/g;s/R_PAREN/")"/g' | \
sed 's/L_CU_BRACKET/"{"/g;s/R_CU_BRACKET/"}"/g' | \
sed 's/L_SQ_BRACKET/"["/g;s/R_SQ_BRACKET/"]"/g' | \
sed 's/SEMICOLON/";"/g;s/COLON/";"/g;s/COMMA/","/g' | \
sed 's/BACKQUOTE/"`"/g' | \
sed 's/EQUIV/"≡"/g' | \
sed 's/HOOK_ARROW/"↪"/g' |
sed 's/LAMBDA/"λ"/g;s/PI/"Π"/g;s/ASSIGN/"≔"/g' > $@
