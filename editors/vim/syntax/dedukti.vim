" Vim syntax file
" Language:        Dedukti
" Maintainer:      Rodolphe Lepigre <rodolphe.lepigre@inri.fr>
" Last Change:     24/10/2017
" Version:         1.0
" Original Author: Rodolphe Lepigre <rodolphe.lepigre@inri.fr>

if exists("b:current_syntax")
  finish
endif

" Keywords
syntax keyword Type Type
syntax keyword Keyword def thm
syntax match   Keyword "\["
syntax match   Keyword "\]"
syntax match   Keyword "("
syntax match   Keyword ")"
syntax match   Keyword ":"
syntax match   Keyword "=>"
syntax match   Keyword ":="
syntax match   Keyword "->"
syntax match   Keyword "-->"
syntax match   Keyword ","
syntax match   Keyword "\."

" Commands
syntax match Include "#EVAL"
syntax match Include "#INFER"
syntax match Include "#CHECK"
syntax match Include "#CHECKNOT"
syntax match Include "#ASSERT"
syntax match Include "#ASSERTNOT"
syntax match Include "#REQUIRE"
syntax match Include "#PROOF"
syntax match Include "#REFINE"
syntax match Include "#REWRITE"
syntax match Include "#QED"
syntax match Include "#FOCUS"
syntax match Include "#SIMPL"
syntax match Include "#PRINT"

" Comments
syn keyword Todo contained TODO FIXME NOTE
syn region Comment start="(;" end=";)" contains=Todo,Comment


