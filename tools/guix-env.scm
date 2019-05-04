;; Environment manifest to build with guix, invoke
;; guix environment -m guix-env.scm

(specifications->manifest
 '("dune"
   "ocaml"
   "ocaml-findlib"
   "ocaml-menhir"
   "ocaml-biniou"
   "ocaml-easy-format"
   "ocaml-yojson"

   "ocaml-base"
   "ocaml-ppx-inline-test"
   "ocaml-ppxlib"
   "ocaml-cmdliner"

   "graphviz"

   "ocaml-bindlib"
   "ocaml-earley"
   "ocaml-timed"))
