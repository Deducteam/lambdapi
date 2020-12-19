" Vim syntax file
" Language:        Lambdapi
" Maintainer:      Rodolphe Lepigre <lepigre@mpi-sws.org>
" Last Change:     12/09/2018
" Version:         1.0
" Original Author: Rodolphe Lepigre <lepigre@mpi-sws.org>

if exists("b:current_syntax")
  finish
endif

" Single-line comments.
syntax keyword Todo contained TODO FIXME NOTE
syntax region Comment start="//\($\|[^/]\)" end="$" contains=Todo

" Documentation comments (FIXME).
syntax include @markdown syntax/markdown.vim
syntax region Comment start="///" end="$" contains=@markdown

" Natural number.
syntax match NaturalNumber "\<[0-9]\+\>"
highlight link NaturalNumber PreProc

" String literal.
syntax match StringLiteral "["][^"]*["]"
highlight link StringLiteral String

" Keywords.
syntax keyword KeywordOK contained abort
syntax keyword KeywordOK contained admit
syntax keyword KeywordOK contained apply
syntax keyword KeywordOK contained as
syntax keyword KeywordOK contained assert
syntax keyword KeywordOK contained assertnot
syntax keyword KeywordOK contained assume
syntax keyword KeywordOK contained begin
syntax keyword KeywordOK contained compute
syntax keyword KeywordOK contained constant
syntax keyword KeywordOK contained end
syntax keyword KeywordOK contained focus
syntax keyword KeywordOK contained in
syntax keyword KeywordOK contained injective
syntax keyword KeywordOK contained let
syntax keyword KeywordOK contained opaque
syntax keyword KeywordOK contained open
syntax keyword KeywordOK contained print
syntax keyword KeywordOK contained private
syntax keyword KeywordOK contained proofterm
syntax keyword KeywordOK contained protected
syntax keyword KeywordOK contained refine
syntax keyword KeywordOK contained reflexivity
syntax keyword KeywordOK contained require
syntax keyword KeywordOK contained rewrite
syntax keyword KeywordOK contained rule
syntax keyword KeywordOK contained set
syntax keyword KeywordOK contained simpl
syntax keyword KeywordOK contained symmetry
syntax keyword KeywordOK contained symbol
syntax keyword KeywordOK contained type
syntax keyword KeywordOK contained TYPE
syntax keyword KeywordOK contained why3
syntax keyword KeywordOK contained with
highlight link KeywordOK Keyword

" Keyword in identifier.
syntax keyword KeywordKO contained abort
syntax keyword KeywordKO contained admit
syntax keyword KeywordKO contained and
syntax keyword KeywordKO contained apply
syntax keyword KeywordKO contained as
syntax keyword KeywordKO contained assert
syntax keyword KeywordKO contained assertnot
syntax keyword KeywordKO contained assume
syntax keyword KeywordKO contained begin
syntax keyword KeywordKO contained compute
syntax keyword KeywordKO contained constant
syntax keyword KeywordKO contained end
syntax keyword KeywordKO contained focus
syntax keyword KeywordKO contained in
syntax keyword KeywordKO contained injective
syntax keyword KeywordKO contained let
syntax keyword KeywordKO contained opaque
syntax keyword KeywordKO contained open
syntax keyword KeywordKO contained print
syntax keyword KeywordKO contained private
syntax keyword KeywordKO contained proofterm
syntax keyword KeywordKO contained protected
syntax keyword KeywordKO contained refine
syntax keyword KeywordKO contained reflexivity
syntax keyword KeywordKO contained require
syntax keyword KeywordKO contained rewrite
syntax keyword KeywordKO contained rule
syntax keyword KeywordKO contained set
syntax keyword KeywordKO contained simpl
syntax keyword KeywordKO contained symmetry
syntax keyword KeywordKO contained symbol
syntax keyword KeywordKO contained type
syntax keyword KeywordKO contained TYPE
syntax keyword KeywordKO contained why3
highlight link KeywordKO Error

" Escaped identifiers member.
syntax region EscapedIdentifier contained matchgroup=Identifier start="{|" end="|}"
highlight link EscapedIdentifier String

" Normal identifiers member.
syntax match IdentifierNotKeyword "\<\h\w*\>" contained contains=KeywordKO
syntax match IdentifierOrAKeyword "\<\h\w*\>" contained contains=KeywordOK
"highlight link NormalIdentifier Identifier

" Qualified identifiers.
syntax match Identifier
  \ "\(\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)\.\)\+\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)"
  \ contains=EscapedIdentifier,IdentifierNotKeyword

" Non-qualified identifier (or keyword).
syntax match Identifier
  \ "\(\<\h\w*\>\|\({|\([^|]\|\n\|\(|[^}]\)\)*|*|}\)\)\.\@!"
  \ contains=EscapedIdentifier,IdentifierOrAKeyword

" Special symbols.
syntax match Keyword "@"
syntax match Keyword ":"
syntax match Keyword "↪"
syntax match Keyword "→"
syntax match Keyword "Π"
syntax match Keyword "λ"
syntax match Keyword "≔"
syntax match Keyword ","
syntax match Keyword ";"
syntax match Keyword "_"
syntax match Keyword "="

" Other special classes.
syntax match Type "\u\w*"
syntax match Constant "&\(\<\h\w*\>\|\({|\([^|]\|\(|[^}]\)\)*|*|}\)\)"
syntax match PreProc  "?\(\<\h\w*\>\|\({|\([^|]\|\(|[^}]\)\)*|*|}\)\)"

" Abbreviations.
abbreviate --> ↪
abbreviate -> →
abbreviate !  Π
abbreviate (! (Π
abbreviate := ≔
abbreviate \  λ
abbreviate (\ (λ
