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
	echo "<qid> ::= [<id>'.']+<id>\n" > $@
	echo "<switch> ::= 'on'\n           | 'off'\n" >> $@
	echo "<assoc> ::= 'left'\n          | 'right'\n" >> $@
	$(BNF_GEN) ../src/core/lpParser.mly | sed \
	-e 's/SWITCH/<switch>/g' \
	-e 's/ASSOC/<assoc>/g' \
	-e 's/ABORT/"abort"/g' \
	-e 's/ADMIT/"admit"/g' \
	-e 's/APPLY/"apply"/g' \
	-e 's/AS/"as"/g' \
	-e 's/"as"SERT/"assert"/g' \
	-e 's/"assert"_NOT/"assertnot"/g' \
	-e 's/"as"SUME/"assume"/g' \
	-e 's/BEGIN/"begin"/g' \
	-e 's/BUILTIN/"builtin"/g' \
	-e 's/COMPUTE/"compute"/g' \
	-e 's/CONSTANT/"constant"/g' \
	-e 's/DEBUG/"debug"/g' \
	-e 's/END/"end"/g' \
	-e 's/FAIL/"fail"/g' \
	-e 's/FLAG/"flag"/g' \
	-e 's/FOCUS/"focus"/g' \
	-e 's/IN/"in"/g' \
	-e 's/"in"DUCTIVE/"inductive"/g' \
	-e 's/"in"FIX/"infix"/g' \
	-e 's/"in"JECTIVE/"injective"/g' \
	-e 's/LET/"let"/g' \
	-e 's/OPEN/"open"/g' \
	-e 's/OPAQUE/"opaque"/g' \
	-e 's/PREFIX/"prefix"/g' \
	-e 's/PR"in"T/"print"/g' \
	-e 's/PRIVATE/"private"/g' \
	-e 's/PROOFTERM/"proofterm"/g' \
	-e 's/PROTECTED/"protected"/g' \
	-e 's/PROVER_TIMEOUT/"prover_timeout"/g' \
	-e 's/PROVER/"prover"/g' \
	-e 's/QUANTIFIER/"quantifier"/g' \
	-e 's/REF"in"E/"refine"/g' \
	-e 's/REFLEXIVITY/"reflexivity"/g' \
	-e 's/REQUIRE/"require"/g' \
	-e 's/REWRITE/"rewrite"/g' \
	-e 's/RULE/"rule"/g' \
	-e 's/SEQUENTIAL/"sequential"/g' \
	-e 's/SET/"set"/g' \
	-e 's/SIMPL/"simpl"/g' \
	-e 's/SOLVE/"solve"/g' \
	-e 's/SYMBOL/"symbol"/g' \
	-e 's/SYMMETRY/"symmetry"/g' \
	-e 's/TYPE_QUERY/"type"/g' \
	-e 's/TYPE_TERM/"TYPE"/g' \
	-e 's/UNIF_"rule"/"unif_rule"/g' \
	-e 's/VERBOSE/"verbose"/g' \
	-e 's/WHY3/"why3"/g' \
	-e 's/WITH/"with"/g' \
	-e 's/"debug"_"flag"S/("+" | "-")<string>/g' \
	-e 's/"in"T/<int>/g' \
	-e 's/FLOAT/<float>/g' \
	-e 's/STR"in"GLIT/<stringlit>/g' \
	-e 's/"as"SIGN/"≔"/g' \
	-e 's/ARROW/→/g' \
	-e 's/BACKQUOTE/"`"/g' \
	-e 's/COMMA/","/g' \
	-e 's/COLON/":"/g' \
	-e 's/EQUIV/"≡"/g' \
	-e 's/HOOK_→/"↪"/g' \
	-e 's/LAMBDA/"λ"/g' \
	-e 's/L_CU_BRACKET/"{"/g' \
	-e 's/L_PAREN/"("/g' \
	-e 's/L_SQ_BRACKET/"["/g' \
	-e 's/PI/"Π"/g' \
	-e 's/R_CU_BRACKET/"}"/g' \
	-e 's/R_PAREN/")"/g' \
	-e 's/R_SQ_BRACKET/"]"/g' \
	-e 's/SEMI"."/";"/g' \
	-e 's/TURNSTILE/"⊢"/g' \
	-e 's/VBAR/"|"/g' \
	-e 's/WILD/"_"/g' \
	-e 's/ID/<id>/g' \
	-e 's/<id>_META/"?"<id>/g' \
	-e 's/<id>_PAT/"$$"<id>/g' \
	-e 's/Q<id>/<qid>/g' \
	-e 's/<qid>_EXPL/"@"<qid>/g' \
	-e "s/\"/\'/g" \
	-e 's/<stringlit>/"<string>"/g' \
	-e 's/| EOF//g' \
	>> $@
