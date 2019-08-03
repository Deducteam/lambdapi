(** Representation of trees as graphviz files.

    {{:https://graphviz.org}Graphviz} is a graph visualization software.  This
    module handle the conversion from {!type:Dtree.t} data structures files in
    the [dot] language that can be interpreted by graphviz.

    A [dot] file [tree.gv] can be converted to a [png] file [tree.png] using
    [dot -Tpng tree.gv > tree.png].  For more output formats,
    @see <https://graphviz.gitlab.io/_pages/doc/info/output.html>

    To output to [tex], one can use
    {{:https://dot2tex.readthedocs.io/}dot2tex}. *)

open Timed
open Extra
open Terms
open Tree_types

(** The type of trees that are written to files. *)
type t = Dtree.t

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of tvar
  | DotCons of TC.t
  | DotSuccess
  | DotFailure

(** [to_dot f t] creates a dot graphviz file [f].gv for tree [t].  Each node
    of the tree embodies a pattern matrix.  The label of a node is the
    column index in the matrix on which the matching is performed to give
    birth to children nodes.  The label on the edge between a node and one of
    its children represents the term matched to generate the next pattern
    matrix (the one of the child node); and is therefore one of the terms in
    the column of the pattern matrix whose index is the label of the node. *)
let to_dot : string -> sym -> unit = fun fname s ->
  let output_tree : t pp = fun oc tree ->
    let pp_dotterm : dot_term pp = fun oc dh ->
      let out fmt = Format.fprintf oc fmt in
      match dh with
      | DotAbst(v)           -> out "λ%a" Print.pp_tvar v
      | DotDefa              -> out "*"
      | DotCons(Symb(a,n,_)) -> out "%s<sub>%d</sub>" n a
      | DotCons(Vari(s))     -> out "%s" s
      | DotCons(Abst)        -> assert false
      | DotSuccess           -> out "✓"
      | DotFailure           -> out "✗"
    in
    let pp_tcstr : term tree_constraint pp = fun oc cstr ->
      let out fmt = Format.fprintf oc fmt in
      let pp_ar oc ar =
        Format.pp_print_list Print.pp_tvar oc (Array.to_list ar)
      in
      match cstr with
      | Constr_Eq(i, j) -> out "@%d≡<sub>v</sub>@%d" i j
      | Constr_FV(vs,i) -> out "%a@@<sub>v</sub>%d" pp_ar vs i
    in
    let out fmt = Format.fprintf oc fmt in
    let node_count = ref 0 in
    (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
       switch on [u] ({!constructor:None} if default). *)
    let rec write_tree : int -> dot_term -> t -> unit = fun father_l swon t ->
      incr node_count;
      match t with
      | Leaf(_, a)  ->
          let _, acte = Bindlib.unmbind a in
          out "@ %d [label=\"%a\"];" !node_count Print.pp acte;
          out "@ %d -- %d [label=<%a>];" father_l !node_count pp_dotterm swon
      | Node({swap; children; store; abstraction=abs; default}) ->
          let tag = !node_count in
          (* Create node *)
          out "@ %d [label=\"@%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "");
          (* Create edge *)
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          TCMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
          Option.iter (fun (v, t) -> write_tree tag (DotAbst(v)) t) abs;
          Option.iter (write_tree tag DotDefa) default
      | Cond({ ok ; cond ; fail }) ->
          let tag = !node_count in
          out "@ %d [label=<%a> shape=\"diamond\"];" tag pp_tcstr cond;
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          write_tree tag DotSuccess ok;
          write_tree tag DotFailure fail
      | Fail        ->
          out "@ %d [label=<!>];" !node_count;
          out "@ %d -- %d [label=\"!\"];" father_l !node_count
    in
    out "graph {@[<v>";
    begin
      match tree with
      (* First step must be done to avoid drawing a top node. *)
      | Node({ swap ; store ; children; default ; abstraction }) ->
          out "@ 0 [label=\"@%d\"%s];" swap
            (if store then " shape=\"box\"" else "");
          TCMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
          Option.iter (fun (v, t) -> write_tree 0 (DotAbst(v)) t) abstraction;
          Option.iter (fun t -> write_tree 0 DotDefa t) default
      | Leaf(_) -> ()
      | _       -> assert false
    end;
    out "@.}@\n@?"
  in
  let tree = Lazy.force (snd !(s.sym_tree)) in
  let oc = open_out fname in
  output_tree (Format.formatter_of_out_channel oc) tree;
  close_out oc
