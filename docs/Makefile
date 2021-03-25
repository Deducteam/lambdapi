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

.PHONY: syntax.bnf
syntax.bnf:
	echo "<qid> ::= [<uid>.]+<uid>\n" > $@
	echo "<switch> ::= on\n           | off\n" >> $@
	echo "<assoc> ::= left\n          | right\n" >> $@
	$(BNF_GEN) ../src/parsing/lpParser.mly | sed \
	-e 's/SWITCH/<switch>/g' \
	-e 's/ASSOC/<assoc>/g' \
	-e 's/ABORT/abort/g' \
	-e 's/ADMIT/admit/g' \
	-e 's/admitTED/admitted/g' \
	-e 's/APPLY/apply/g' \
	-e 's/AS/as/g' \
	-e 's/asSERT/assert/g' \
	-e 's/assertNOT/assertnot/g' \
	-e 's/asSUME/assume/g' \
	-e 's/BEGIN/begin/g' \
	-e 's/BUILTIN/builtin/g' \
	-e 's/COMPUTE/compute/g' \
	-e 's/CONSTANT/constant/g' \
	-e 's/DEBUG/debug/g' \
	-e 's/END/end/g' \
	-e 's/FAIL/fail/g' \
	-e 's/FLAG/flag/g' \
	-e 's/FOCUS/focus/g' \
	-e 's/HAVE/have/g' \
	-e 's/IN/in/g' \
	-e 's/inDUCTION/induction/g' \
	-e 's/inDUCTIVE/inductive/g' \
	-e 's/inFIX/infix/g' \
	-e 's/inJECTIVE/injective/g' \
	-e 's/LET/let/g' \
	-e 's/NOTATION/notation/g' \
	-e 's/OPEN/open/g' \
	-e 's/OPAQUE/opaque/g' \
	-e 's/PREFIX/prefix/g' \
	-e 's/PRinT/print/g' \
	-e 's/PRIVATE/private/g' \
	-e 's/PROOFTERM/proofterm/g' \
	-e 's/PROTECTED/protected/g' \
	-e 's/PROVER_TIMEOUT/prover_timeout/g' \
	-e 's/PROVER/prover/g' \
	-e 's/QUANTIFIER/quantifier/g' \
	-e 's/REFinE/refine/g' \
	-e 's/REFLEXIVITY/reflexivity/g' \
	-e 's/REQUIRE/require/g' \
	-e 's/REWRITE/rewrite/g' \
	-e 's/RULE/rule/g' \
	-e 's/SEQUENTIAL/sequential/g' \
	-e 's/SIMPL/simpl/g' \
	-e 's/SOLVE/solve/g' \
	-e 's/SYMBOL/symbol/g' \
	-e 's/SYMMETRY/symmetry/g' \
	-e 's/TYPE_QUERY/type/g' \
	-e 's/TYPE_TERM/TYPE/g' \
	-e 's/UNIF_rule/unif_rule/g' \
	-e 's/VERBOSE/verbose/g' \
	-e 's/WHY3/why3/g' \
	-e 's/WITH/with/g' \
	-e 's/debug_flagS/(+ | -)<string>/g' \
	-e 's/inT/<int>/g' \
	-e 's/FLOAT/<float>/g' \
	-e 's/STRinGLIT/<stringlit>/g' \
	-e 's/asSIGN/≔/g' \
	-e 's/ARROW/→/g' \
	-e 's/BACKQUOTE/`/g' \
	-e 's/COMMA/,/g' \
	-e 's/COLON/:/g' \
	-e 's/EQUIV/≡/g' \
	-e 's/HOOK_→/↪/g' \
	-e 's/LAMBDA/λ/g' \
	-e 's/L_CU_BRACKET/{/g' \
	-e 's/L_PAREN/(/g' \
	-e 's/L_SQ_BRACKET/[/g' \
	-e 's/PI/Π/g' \
	-e 's/R_CU_BRACKET/}/g' \
	-e 's/R_PAREN/)/g' \
	-e 's/R_SQ_BRACKET/]/g' \
	-e 's/SEMI./;/g' \
	-e 's/TURNSTILE/⊢/g' \
	-e 's/VBAR/|/g' \
	-e 's/WILD/_/g' \
	-e 's/<uid> ::= UID//g' \
	-e 's/UID/<uid>/g' \
	-e 's/<uid>_META/?<uid>/g' \
	-e 's/<uid>_PAT/$$<uid>/g' \
	-e 's/QID/<qid>/g' \
	-e 's/ID_EXPL/@<id>/g' \
	-e 's/<stringlit>/\"<string>\"/g' \
	-e 's/| EOF//g' \
	>> $@

.PHONY: syntax_dedukti.bnf
syntax_dedukti.bnf:
	echo "<qid> ::= [<uid>.]+<uid>\n" > $@
	echo "<assert> ::= #ASSERT\n           | #ASSERTNOT\n" >> $@
	$(BNF_GEN) ../src/parsing/dkParser.mly | sed \
	-e 's/ASSERT/<assert>/g' \
	-e 's/EVAL/#EVAL/g' \
	-e 's/KW_DEF/def/g' \
	-e 's/KW_INJ/injective/g' \
	-e 's/KW_PRV/private/g' \
	-e 's/KW_THM/thm/g' \
	-e 's/INFER/#INFER/g' \
	-e 's/REQUIRE/#REQUIRE <qid>/g' \
	-e 's/TYPE/Type/g' \
	-e 's/ARROW/->/g' \
	-e 's/COLON/:/g' \
	-e 's/COMMA/,/g' \
	-e 's/DEF/:=/g' \
	-e 's/DOT/./g' \
	-e 's/EQUAL/==/g' \
	-e 's/FAT->/=>/g' \
	-e 's/LONG->/-->/g' \
	-e 's/LEFTPAR/(/g' \
	-e 's/LEFTSQU/[/g' \
	-e 's/RIGHTPAR/)/g' \
	-e 's/RIGHTSQU/]/g' \
	-e 's/UNDERSCORE/_/g' \
	-e 's/UID/<uid>/g' \
	-e 's/QID/<qid>/g' \
	-e 's/| EOF//g' \
	>> $@
