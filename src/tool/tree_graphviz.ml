(** Representation of trees as graphviz files.

    {{:https://graphviz.org}Graphviz} is a graph visualization software.  This
    module handles the conversion from {!type:Tree.t} data structures files in
    the [dot] language that can be interpreted by graphviz.

    See the chapter [doc/options.md#printing-decision-trees] of the
    documentation for more information. *)

open! Lplib
open Lplib.Base

open Timed
open Core
open Term
open Tree_type

(** Printing hint for conversion to graphviz. *)
type dot_term =
  | DotDefa (* Default case *)
  | DotAbst of int
  | DotProd of int
  | DotCons of TC.t
  | DotSuccess
  | DotFailure

(** [to_dot oc sym] prints a dot graphviz representation of the tree of symbol
    [sym] on output channel [oc]. Each node of the tree embodies a pattern
    matrix. The label of a node is the column index in the matrix on which the
    matching is performed to give birth to the child node. The label on the
    edge between a node and one of its children represents the term matched to
    generate the next pattern matrix (the one of the child node). *)
let to_dot : Format.formatter -> sym -> unit = fun oc s ->
  let output_tree oc tree =
    let pp_dotterm : dot_term pp = fun oc dh ->
      let out fmt = Format.fprintf oc fmt in
      let var_px = "v" in
      match dh with
      | DotAbst(id)          -> out "λ%s%d" var_px id
      | DotProd(id)          -> out "Π%s%d" var_px id
      | DotDefa              -> out "*"
      | DotCons(Symb(_,n,a)) -> out "%s<sub>%d</sub>" n a
      | DotCons(Vari(i))     -> out "%s%d" var_px i
      | DotSuccess           -> out "✓"
      | DotFailure           -> out "✗"
    in
    let pp_tcstr : tree_cond pp = fun oc cstr ->
      let out fmt = Format.fprintf oc fmt in
      let pp_ar = Array.pp Format.pp_print_int " "
      in
      match cstr with
      | CondNL(i, j) -> out "%d ≡ %d" i j
      | CondFV(i,vs) -> out "%a ⊊ FV(%d)" pp_ar vs i
    in
    let out fmt = Format.fprintf oc fmt in
    let node_count = ref 0 in
    (* [write_tree n u v] writes tree [v] obtained from tree number [n] with a
       switch on [u] ({!constructor:None} if default). *)
    let rec write_tree father_l swon t =
      incr node_count;
      match t with
      | Leaf(_,(a,_))                                                    ->
          let _, acte = Bindlib.unmbind a in
          out "@ %d [label=\"%a\"];" !node_count Print.pp_term acte;
          out "@ %d -- %d [label=<%a>];" father_l !node_count pp_dotterm swon
      | Node({swap; children; store; abstraction=abs; default; product}) ->
          let tag = !node_count in
          (* Create node *)
          out "@ %d [label=\"@%d\"%s];" tag swap
            (if store then " shape=\"box\"" else "");
          (* Create edge *)
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          TCMap.iter (fun s e -> write_tree tag (DotCons(s)) e) children;
          Option.iter (fun (x,t) -> write_tree tag (DotAbst(x)) t) abs;
          Option.iter (fun (x,t) -> write_tree tag (DotProd(x)) t) product;
          Option.iter (write_tree tag DotDefa) default
      | Cond({ ok ; cond ; fail })                                       ->
          let tag = !node_count in
          out "@ %d [label=<%a> shape=\"diamond\"];" tag pp_tcstr cond;
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          write_tree tag DotSuccess ok;
          write_tree tag DotFailure fail
      | Eos(l,r)                                                         ->
          let tag = !node_count in
          out "@ %d [label=\"\" shape=\"triangle\"];" tag;
          out "@ %d -- %d [label=<%a>];" father_l tag pp_dotterm swon;
          write_tree tag DotFailure l;
          write_tree tag DotSuccess r
      | Fail                                                             ->
          out "@ %d [label=<!>];" !node_count;
          out "@ %d -- %d [label=\"!\"];" father_l !node_count
    in
    out "graph {@[<v>";
    begin
      match tree with
      (* First step must be done to avoid drawing a top node. *)
      | Node{swap; store; children; default; abstraction; product} ->
          out "@ 0 [label=\"@%d\"%s];" swap
            (if store then " shape=\"box\"" else "");
          TCMap.iter (fun sw c -> write_tree 0 (DotCons(sw)) c) children;
          Option.iter (fun (x,t) -> write_tree 0 (DotAbst(x)) t) abstraction;
          Option.iter (fun (x,t) -> write_tree 0 (DotProd(x)) t) product;
          Option.iter (fun t -> write_tree 0 DotDefa t) default
      | Leaf(_) -> ()
      | _       -> assert false
    end;
    out "@.}@\n@?"
  in
  output_tree oc (Lazy.force (snd !(s.sym_tree)))
